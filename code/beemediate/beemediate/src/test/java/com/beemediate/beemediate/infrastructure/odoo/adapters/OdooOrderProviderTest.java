package com.beemediate.beemediate.infrastructure.odoo.adapters;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.doNothing;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.time.LocalDateTime;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.Before;
import org.junit.Test;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.infrastructure.odoo.OdooOrderProvider;
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.ArticoloPreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.CompagniaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ContattoConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.DestinazioneDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoFornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

public class OdooOrderProviderTest {

    private OdooApiConfig odooMock;
    private OdooOrderProvider provider;

    @Before
    public void setUp() {
        odooMock = mock(OdooApiConfig.class);
        provider = new OdooOrderProvider(odooMock);
    }

    @Test
    public void fetchOrders_happyPath_buildsOrder() {
        // Preparazione mocks DTO e comportamenti
        when(odooMock.isOnline()).thenReturn(true);

        FornitoreDTO fornitore = mock(FornitoreDTO.class);
        PreventivoDTO preventivo = mock(PreventivoDTO.class);
        ConsegnaDTO consegna = mock(ConsegnaDTO.class);
        ContattoConsegnaDTO contatto = mock(ContattoConsegnaDTO.class);
        DestinazioneDTO destinazione = mock(DestinazioneDTO.class);
        CompagniaDTO compagnia = mock(CompagniaDTO.class);
        ArticoloPreventivoDTO art = mock(ArticoloPreventivoDTO.class);
        ArticoloPreventivoDTO[] artArr = new ArticoloPreventivoDTO[]{art};
        ProdottoDTO prodDto = mock(ProdottoDTO.class);
        ProdottoDTO[] prodDtoArr = new ProdottoDTO[]{prodDto};
        ProdottoFornitoreDTO prodf = mock(ProdottoFornitoreDTO.class);
        ProdottoFornitoreDTO[] prodfArr = new ProdottoFornitoreDTO[]{prodf};

        // Mock statici delle factory DTO
        try (MockedStatic<FornitoreDTO> mockF = Mockito.mockStatic(FornitoreDTO.class);
             MockedStatic<PreventivoDTO> mockP = Mockito.mockStatic(PreventivoDTO.class);
             MockedStatic<ConsegnaDTO> mockC = Mockito.mockStatic(ConsegnaDTO.class);
             MockedStatic<ContattoConsegnaDTO> mockCC = Mockito.mockStatic(ContattoConsegnaDTO.class);
             MockedStatic<DestinazioneDTO> mockD = Mockito.mockStatic(DestinazioneDTO.class);
             MockedStatic<CompagniaDTO> mockComp = Mockito.mockStatic(CompagniaDTO.class);
             MockedStatic<ArticoloPreventivoDTO> mockAP = Mockito.mockStatic(ArticoloPreventivoDTO.class);
             MockedStatic<ProdottoDTO> mockProd = Mockito.mockStatic(ProdottoDTO.class);
             MockedStatic<ProdottoFornitoreDTO> mockPF = Mockito.mockStatic(ProdottoFornitoreDTO.class)) {

            mockF.when(() -> FornitoreDTO.fromXMLRPC(odooMock)).thenReturn(fornitore);
            mockP.when(() -> PreventivoDTO.fromXMLRPC(odooMock, fornitore)).thenReturn(preventivo);
            mockC.when(() -> ConsegnaDTO.fromXMLRPC(odooMock, preventivo)).thenReturn(consegna);
            mockCC.when(() -> ContattoConsegnaDTO.fromXMLRPC(odooMock, consegna)).thenReturn(contatto);
            mockD.when(() -> DestinazioneDTO.fromXMLRPC(odooMock, contatto)).thenReturn(destinazione);
            mockComp.when(() -> CompagniaDTO.fromXMLRPC(odooMock, preventivo)).thenReturn(compagnia);

            mockAP.when(() -> ArticoloPreventivoDTO.fromXMLRPC(odooMock, preventivo)).thenReturn(artArr);
            mockProd.when(() -> ProdottoDTO.fromXMLRPC(odooMock, artArr)).thenReturn(prodDtoArr);
            mockPF.when(() -> ProdottoFornitoreDTO.fromXMLRPC(odooMock, prodDtoArr, fornitore)).thenReturn(prodfArr);

            // Mock dei getter usati da OrderMapper (header e item fields)
            when(preventivo.getName()).thenReturn(Optional.of("ORD-1"));

            IdentifierDTO currencyIdMock = mock(IdentifierDTO.class);
            when(preventivo.getCurrencyId()).thenReturn(currencyIdMock);
            when(currencyIdMock.getName()).thenReturn(Optional.of("EUR"));

            when(compagnia.getCompanyRegistry()).thenReturn(Optional.of("COMP-REG"));
            when(fornitore.getCodiceAzienda()).thenReturn(Optional.of("SUP-123"));
            when(destinazione.getCodiceDestinazione()).thenReturn(Optional.of("DEST-1"));

            LocalDateTime odt = LocalDateTime.of(2021, 1, 2, 3, 4, 5);
            LocalDateTime pdt = LocalDateTime.of(2021, 1, 3, 0, 0, 0);
            when(preventivo.getDateOrder()).thenReturn(Optional.of(odt));
            when(preventivo.getDatePlanned()).thenReturn(Optional.of(pdt));

            when(art.getProductQty()).thenReturn(Optional.of(2.0));

            IdentifierDTO prodIdMock = mock(IdentifierDTO.class);
            when(prodf.getProductId()).thenReturn(prodIdMock);
            when(prodIdMock.getName()).thenReturn(Optional.of("BUYER-1"));
            when(prodf.getProductCode()).thenReturn(Optional.of("SUP-CODE"));
            when(prodf.getProductName()).thenReturn(Optional.of("ShortDesc"));
            when(prodf.getSequence()).thenReturn(Optional.of(1));
            IdentifierDTO uomMock = mock(IdentifierDTO.class);
            when(prodf.getProductUomId()).thenReturn(uomMock);
            when(uomMock.getName()).thenReturn(Optional.of("PCS"));

            // Esegui
            boolean fetched = provider.fetchOrders();

            // Verifiche
            assertTrue("fetchOrders dovrebbe ritornare true nel percorso felice", fetched);
            assertTrue("hasNewOrder deve essere true dopo fetchOrders felice", provider.hasNewOrder());

            Order created = provider.popNewOrder();
            assertNotNull("popNewOrder non deve restituire null dopo fetchOrders felice", created);

            
            
            assertEquals("ORD-1", created.getOrderID());

            // dopo pop il buffer è vuoto
            assertFalse(provider.hasNewOrder());
        }
    }

    @Test
    public void fetchOrders_whenFornitoreXmlRpcException_fetchOrdersFalse()  {
        when(odooMock.isOnline()).thenReturn(true);

        try (MockedStatic<FornitoreDTO> mockF = Mockito.mockStatic(FornitoreDTO.class)) {
            mockF.when(() -> FornitoreDTO.fromXMLRPC(odooMock)).thenThrow(new XmlRpcException("xmlrpc"));

            boolean res = provider.fetchOrders();
            assertFalse("fetchOrders deve ritornare false quando XmlRpcException è lanciata", res);
            assertFalse(provider.hasNewOrder());
        }
    }

    @Test
    public void fetchOrders_whenArticoloEmptyFetchHandled_returnsFalse_noOrder() {
        when(odooMock.isOnline()).thenReturn(true);

        FornitoreDTO fornitore = mock(FornitoreDTO.class);
        PreventivoDTO preventivo = mock(PreventivoDTO.class);

        try (MockedStatic<FornitoreDTO> mockF = Mockito.mockStatic(FornitoreDTO.class);
             MockedStatic<PreventivoDTO> mockP = Mockito.mockStatic(PreventivoDTO.class);
             MockedStatic<ConsegnaDTO> mockC = Mockito.mockStatic(ConsegnaDTO.class);
             MockedStatic<ContattoConsegnaDTO> mockCC = Mockito.mockStatic(ContattoConsegnaDTO.class);
             MockedStatic<DestinazioneDTO> mockD = Mockito.mockStatic(DestinazioneDTO.class);
             MockedStatic<CompagniaDTO> mockComp = Mockito.mockStatic(CompagniaDTO.class);
             MockedStatic<ArticoloPreventivoDTO> mockAP = Mockito.mockStatic(ArticoloPreventivoDTO.class)) {

            mockF.when(() -> FornitoreDTO.fromXMLRPC(odooMock)).thenReturn(fornitore);
            mockP.when(() -> PreventivoDTO.fromXMLRPC(odooMock, fornitore)).thenReturn(preventivo);

            ConsegnaDTO consegna = mock(ConsegnaDTO.class);
            ContattoConsegnaDTO contatto = mock(ContattoConsegnaDTO.class);
            DestinazioneDTO destinazione = mock(DestinazioneDTO.class);
            CompagniaDTO compagnia = mock(CompagniaDTO.class);

            mockC.when(() -> ConsegnaDTO.fromXMLRPC(odooMock, preventivo)).thenReturn(consegna);
            mockCC.when(() -> ContattoConsegnaDTO.fromXMLRPC(odooMock, consegna)).thenReturn(contatto);
            mockD.when(() -> DestinazioneDTO.fromXMLRPC(odooMock, contatto)).thenReturn(destinazione);
            mockComp.when(() -> CompagniaDTO.fromXMLRPC(odooMock, preventivo)).thenReturn(compagnia);

            // ArticoloPreventivoDTO.fromXMLRPC solleva EmptyFetchException -> gestito internamente in fetchData
            mockAP.when(() -> ArticoloPreventivoDTO.fromXMLRPC(odooMock, preventivo))
                  .thenThrow(new EmptyFetchException("no items"));

            boolean res = provider.fetchOrders();
            assertFalse("fetchOrders deve restituire false quando EmptyFetchException è sollevata internamente", res);
            assertFalse(provider.hasNewOrder());
        }
    }

    @Test
    public void fetchOrders_whenPreventivoInconsistentHandled_returnsFalse_noOrder() {
        when(odooMock.isOnline()).thenReturn(true);

        FornitoreDTO fornitore = mock(FornitoreDTO.class);

        try (MockedStatic<FornitoreDTO> mockF = Mockito.mockStatic(FornitoreDTO.class);
             MockedStatic<PreventivoDTO> mockP = Mockito.mockStatic(PreventivoDTO.class)) {

            mockF.when(() -> FornitoreDTO.fromXMLRPC(odooMock)).thenReturn(fornitore);
            mockP.when(() -> PreventivoDTO.fromXMLRPC(odooMock, fornitore))
                 .thenThrow(new InconsistentDTOException("inconsistent"));

            boolean res = provider.fetchOrders();
            assertFalse("fetchOrders deve restituire false quando InconsistentDTOException è sollevata internamente", res);
            assertFalse(provider.hasNewOrder());
        }
    }

    @Test
    public void fetchOrders_whenNotOnline_callsConnect_thenProceed() throws Exception {
        when(odooMock.isOnline()).thenReturn(false);
        doNothing().when(odooMock).connect();

        try (MockedStatic<FornitoreDTO> mockF = Mockito.mockStatic(FornitoreDTO.class)) {
            // falliremo subito con XmlRpcException dopo connect, ma vogliamo verificare connect() è chiamato
            mockF.when(() -> FornitoreDTO.fromXMLRPC(odooMock)).thenThrow(new XmlRpcException("xmlrpc"));

            boolean res = provider.fetchOrders();

            // verify connect chiamato perché isOnline era false
            verify(odooMock, times(1)).connect();
            assertFalse(res);
            assertFalse(provider.hasNewOrder());
        }
    }
}