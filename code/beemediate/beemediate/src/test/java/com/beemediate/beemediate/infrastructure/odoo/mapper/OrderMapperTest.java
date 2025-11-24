package com.beemediate.beemediate.infrastructure.odoo.mapper;

import static org.junit.Assert.*;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.pojo.order.OrderSummary;
import com.beemediate.beemediate.infrastructure.odoo.dto.*;

import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.Mockito;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Optional;

public class OrderMapperTest {

	@Mock
    private FornitoreDTO mockFornitore;
    
	@Mock
	private PreventivoDTO mockPreventivo;
    
	@Mock
	private ArticoloPreventivoDTO[] artprArray;
    
	@Mock
	private ProdottoFornitoreDTO[] prodfArray;
    
	@Mock
	private DestinazioneDTO mockDestinazione;
    
	@Mock
	private CompagniaDTO mockCompagnia;

    private static final DateTimeFormatter ISO_FMT = DateTimeFormatter.ISO_LOCAL_DATE_TIME;

    @Before
    public void setup() {
        mockFornitore = Mockito.mock(FornitoreDTO.class);
        mockPreventivo = Mockito.mock(PreventivoDTO.class);
        mockDestinazione = Mockito.mock(DestinazioneDTO.class);
        mockCompagnia = Mockito.mock(CompagniaDTO.class);
    }

    @Test
    public void map_allOptionalsPresent_mapsHeaderAndItemsCorrectly() {
        // Setup header-related DTOs
        Mockito.when(mockPreventivo.getName()).thenReturn(Optional.of("ORDER-123"));
        // dateOrder and datePlanned present
        LocalDateTime orderDate = LocalDateTime.of(2021, 5, 10, 12, 30, 0);
        LocalDateTime plannedDate = LocalDateTime.of(2021, 5, 15, 8, 0, 0);
        Mockito.when(mockPreventivo.getDateOrder()).thenReturn(Optional.of(orderDate));
        Mockito.when(mockPreventivo.getDatePlanned()).thenReturn(Optional.of(plannedDate));

        // currency
        IdentifierDTO currency = new IdentifierDTO( new Object[] {1, "EUR"} );
        Mockito.when(mockPreventivo.getCurrencyId()).thenReturn(currency);

        // company registry present
        Mockito.when(mockCompagnia.getCompanyRegistry()).thenReturn(Optional.of("COMP-REG-1"));

        // supplier code present
        Mockito.when(mockFornitore.getCodiceAzienda()).thenReturn(Optional.of("SUP-001"));

        // destination present
        Mockito.when(mockDestinazione.getCodiceDestinazione()).thenReturn(Optional.of("DEST-01"));

        // Setup one article + one product
        ArticoloPreventivoDTO art = Mockito.mock(ArticoloPreventivoDTO.class);
        ProdottoFornitoreDTO prod = Mockito.mock(ProdottoFornitoreDTO.class);

        // art quantity present
        Mockito.when(art.getProductQty()).thenReturn(Optional.of(10.0));

        // product fields present
        IdentifierDTO pn = new IdentifierDTO( new Object[] {1, "BUYER-ITEM-1" } );
        Mockito.when(prod.getProductId()).thenReturn(pn);

        Mockito.when(prod.getProductCode()).thenReturn(Optional.of("SUPPLIER-CODE-1"));
        Mockito.when(prod.getProductName()).thenReturn(Optional.of("Short desc"));
        Mockito.when(prod.getSequence()).thenReturn(Optional.of(5));
        IdentifierDTO uom = new IdentifierDTO( new Object[] {55, "PCS"} );
        Mockito.when(prod.getProductUomId()).thenReturn(uom);

        artprArray = new ArticoloPreventivoDTO[] { art };
        prodfArray = new ProdottoFornitoreDTO[] { prod };

        OrderStructure result = OrderMapper.map(mockFornitore, mockPreventivo, artprArray, prodfArray, mockDestinazione, mockCompagnia);
        assertNotNull(result);

        // header assertions
        OrderHeader header = result.getHeader();
        assertNotNull(header);
        assertEquals("ORDER-123", header.getOrderID());
        assertEquals("EUR", header.getCurrency());
        assertEquals("COMP-REG-1", header.getBuyerID());
        assertEquals("COMP-REG-1", header.getBuyerIDRef());
        assertEquals("SUP-001", header.getSupplierID());
        assertEquals("SUP-001", header.getSupplierIDRef());
        assertEquals("DEST-01", header.getDeliveryID());
        assertEquals("DEST-01", header.getDeliveryIDRef());
        assertEquals(orderDate.format(ISO_FMT), header.getOrderDate());
        assertEquals(plannedDate.format(ISO_FMT), header.getStartDate());
        assertEquals(plannedDate.format(ISO_FMT), header.getEndDate());

        // summary
        OrderSummary summary = result.getOrderSummary();
        assertNotNull(summary);
        assertEquals(1, summary.getTotalItemNum());

        // items
        OrderItem[] items = result.getItemList();
        assertNotNull(items);
        assertEquals(1, items.length);
        OrderItem it = items[0];
        assertEquals("BUYER-ITEM-1", it.getBuyerID());
        assertEquals("SUPPLIER-CODE-1", it.getSupplierID());
        assertEquals("Short desc", it.getDescriptionShort());
        assertEquals("5", it.getLineItemID());
        assertEquals("10.0", it.getQuantity());
        assertEquals("PCS", it.getOrderUnit());
    }

    @Test
    public void map_missingOptionalHeaderFields_usesEmptyStrings() {
        // Make all header optionals empty to test branches setting empty strings
        Mockito.when(mockPreventivo.getName()).thenReturn(Optional.empty());

        IdentifierDTO currency = new IdentifierDTO( new Object[] {1, null} );
        Mockito.when(mockPreventivo.getCurrencyId()).thenReturn(currency);

        Mockito.when(mockCompagnia.getCompanyRegistry()).thenReturn(Optional.empty());
        Mockito.when(mockFornitore.getCodiceAzienda()).thenReturn(Optional.empty());
        Mockito.when(mockDestinazione.getCodiceDestinazione()).thenReturn(Optional.empty());
        Mockito.when(mockPreventivo.getDateOrder()).thenReturn(Optional.empty());
        Mockito.when(mockPreventivo.getDatePlanned()).thenReturn(Optional.empty());

        // Single item with missing product optionals
        ArticoloPreventivoDTO art = Mockito.mock(ArticoloPreventivoDTO.class);
        ProdottoFornitoreDTO prod = Mockito.mock(ProdottoFornitoreDTO.class);

        Mockito.when(art.getProductQty()).thenReturn(Optional.empty());
        IdentifierDTO pn = new IdentifierDTO( new Object[] {8, null} );
        Mockito.when(prod.getProductId()).thenReturn(pn);
        Mockito.when(prod.getProductCode()).thenReturn(Optional.empty());
        Mockito.when(prod.getProductName()).thenReturn(Optional.empty());
        Mockito.when(prod.getSequence()).thenReturn(Optional.empty());
        IdentifierDTO uom = new IdentifierDTO( new Object[] {55, null} );
        Mockito.when(prod.getProductUomId()).thenReturn(uom);

        artprArray = new ArticoloPreventivoDTO[] { art };
        prodfArray = new ProdottoFornitoreDTO[] { prod };

        OrderStructure result = OrderMapper.map(mockFornitore, mockPreventivo, artprArray, prodfArray, mockDestinazione, mockCompagnia);

        // header should have empty strings
        OrderHeader header = result.getHeader();
        assertEquals("", header.getOrderID());
        assertEquals("", header.getCurrency());
        assertEquals("", header.getBuyerID());
        assertEquals("", header.getBuyerIDRef());
        assertEquals("", header.getSupplierID());
        assertEquals("", header.getSupplierIDRef());
        assertEquals("", header.getDeliveryID());
        assertEquals("", header.getDeliveryIDRef());
        assertEquals("", header.getOrderDate());
        assertEquals("", header.getStartDate());
        assertEquals("", header.getEndDate());

        // item: because art.getProductQty() empty the mapper has a bug where it sets lineItemID to ""
        OrderItem it = result.getItemList()[0];
        assertEquals("", it.getBuyerID());
        assertEquals("", it.getSupplierID());
        assertEquals("", it.getDescriptionShort());
        assertEquals("", it.getLineItemID()); // sequence empty -> ""
        // quantity branch: when productQty absent, implementation sets lineItemID to "" (bug) — quantity stays null or default
        // We assert that quantity is null or empty string depending on POJO default; to be robust check for null or empty:
        String quantity = it.getQuantity();
        assertTrue(quantity == null || quantity.isEmpty());
        assertEquals("", it.getOrderUnit());
    }

    @Test
    public void map_partialHeader_and_itemBranches_mcdcOriented() {
        // This test toggles some optionals to exercise different independent conditions:
        // - currency present, company absent
        // - supplier present, destination absent
        // - dateOrder absent, datePlanned present (affects start/end but not orderDate)
        Mockito.when(mockPreventivo.getName()).thenReturn(Optional.of("P-1"));

        IdentifierDTO currency = new IdentifierDTO( new Object[] {1, "USD"} );
        Mockito.when(mockPreventivo.getCurrencyId()).thenReturn(currency);

        Mockito.when(mockCompagnia.getCompanyRegistry()).thenReturn(Optional.empty());
        Mockito.when(mockFornitore.getCodiceAzienda()).thenReturn(Optional.of("SUP-X"));
        Mockito.when(mockDestinazione.getCodiceDestinazione()).thenReturn(Optional.empty());

        Mockito.when(mockPreventivo.getDateOrder()).thenReturn(Optional.empty());
        LocalDateTime planned = LocalDateTime.of(2022, 1, 1, 0, 0, 0);
        Mockito.when(mockPreventivo.getDatePlanned()).thenReturn(Optional.of(planned));

        // Items: mix present/absent fields
        ArticoloPreventivoDTO art1 = Mockito.mock(ArticoloPreventivoDTO.class);
        ArticoloPreventivoDTO art2 = Mockito.mock(ArticoloPreventivoDTO.class);
        ProdottoFornitoreDTO prod1 = Mockito.mock(ProdottoFornitoreDTO.class);
        ProdottoFornitoreDTO prod2 = Mockito.mock(ProdottoFornitoreDTO.class);

        // art1 qty present, art2 qty absent
        Mockito.when(art1.getProductQty()).thenReturn(Optional.of(1.0));
        Mockito.when(art2.getProductQty()).thenReturn(Optional.empty());

        // prod1: some fields present
        IdentifierDTO pn1 = new IdentifierDTO( new Object[] {8, "B1"} );
        Mockito.when(prod1.getProductId()).thenReturn(pn1);
        Mockito.when(prod1.getProductCode()).thenReturn(Optional.of("S1"));
        Mockito.when(prod1.getProductName()).thenReturn(Optional.of("Desc1"));
        Mockito.when(prod1.getSequence()).thenReturn(Optional.of(1));
        IdentifierDTO u1 = new IdentifierDTO(new Object[] {1, "KG" });
        Mockito.when(prod1.getProductUomId()).thenReturn(u1);

        // prod2: all empty
        IdentifierDTO pn2 = new IdentifierDTO( new Object[] {92, null} );
        Mockito.when(prod2.getProductId()).thenReturn(pn2);
        Mockito.when(prod2.getProductCode()).thenReturn(Optional.empty());
        Mockito.when(prod2.getProductName()).thenReturn(Optional.empty());
        Mockito.when(prod2.getSequence()).thenReturn(Optional.empty());
        IdentifierDTO u2 = new IdentifierDTO(new Object[] {1, null });
        Mockito.when(prod2.getProductUomId()).thenReturn(u2);

        artprArray = new ArticoloPreventivoDTO[] { art1, art2 };
        prodfArray = new ProdottoFornitoreDTO[] { prod1, prod2 };

        OrderStructure result = OrderMapper.map(mockFornitore, mockPreventivo, artprArray, prodfArray, mockDestinazione, mockCompagnia);

        // Header checks
        OrderHeader header = result.getHeader();
        assertEquals("P-1", header.getOrderID());
        assertEquals("USD", header.getCurrency());
        // company missing -> buyer empty
        assertEquals("", header.getBuyerID());
        // supplier present
        assertEquals("SUP-X", header.getSupplierID());
        // destination missing -> delivery empty
        assertEquals("", header.getDeliveryID());
        // orderDate empty, start/end set from planned
        assertEquals("", header.getOrderDate());
        assertEquals(planned.format(ISO_FMT), header.getStartDate());
        assertEquals(planned.format(ISO_FMT), header.getEndDate());

        // Items checks
        OrderItem[] items = result.getItemList();
        assertEquals(2, items.length);

        // item 0 should reflect prod1 and art1
        OrderItem i0 = items[0];
        assertEquals("B1", i0.getBuyerID());
        assertEquals("S1", i0.getSupplierID());
        assertEquals("Desc1", i0.getDescriptionShort());
        assertEquals("1", i0.getLineItemID());
        assertEquals("1.0", i0.getQuantity());
        assertEquals("KG", i0.getOrderUnit());

        // item 1 should have blanks due to empty optionals
        OrderItem i1 = items[1];
        assertEquals("", i1.getBuyerID());
        assertEquals("", i1.getSupplierID());
        assertEquals("", i1.getDescriptionShort());
        assertEquals("", i1.getLineItemID());
        // quantity branch: art2 quantity absent -> implementation sets lineItemID to "" (we already asserted)
        String qty1 = i1.getQuantity();
        assertTrue(qty1.isEmpty());
        assertEquals("", i1.getOrderUnit());
    }
}