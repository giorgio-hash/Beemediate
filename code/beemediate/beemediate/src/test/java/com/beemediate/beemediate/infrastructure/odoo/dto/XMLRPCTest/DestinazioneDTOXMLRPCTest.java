package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.reset;

import java.util.HashMap;
import java.util.Map;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.ContattoConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.DestinazioneDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC
 * 
 * CASE| 		concons == null || concons.getPartnerId().getNum().isEmpty()		|		res.length == 0		| ESITO
 * 0   |			F			F														|			F				| happy path
 * 1   |			F			F														|			T				| EmptyFetchException ("Non trovo informazioni della destinazione.")
 * 2   |			T			-														|			-				| InconsistentDTOException
 * 3   |			F			T														|			-				| InconsistentDTOException
 */
public class DestinazioneDTOXMLRPCTest {

    @Mock
    private OdooApiConfig odoo;

    @Mock
    private ContattoConsegnaDTO concons;

    @Before
    public void setup() {
        MockitoAnnotations.openMocks(this);
    }

    @After
    public void teardown() {
        reset(odoo, concons);
    }

    // 0: happy path -> readFromModel returns a non-empty array with a map
    @Test
    public void testFromXMLRPC_returnsDestinazioneDTO_whenAllGood() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
        final Object partnerId = 77;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { partnerId, "PARTNER-77" });

        Map<String, Object> map = new HashMap<>();
        map.put("id", 77);
        map.put("ref", "DEST-001");

        when(concons.getPartnerId()).thenReturn(idDto);
        // readFromModel is called with (odoo.RES_PARTNER, requestInfo, id)
        when(odoo.readFromModel(eq(odoo.RES_PARTNER), anyMap(), eq(partnerId))).thenReturn(new Object[] { map });

        DestinazioneDTO expected = new DestinazioneDTO(map);
        DestinazioneDTO actual = DestinazioneDTO.fromXMLRPC(odoo, concons);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    // 1: readFromModel returns empty -> EmptyFetchException
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoResourceFound() throws XmlRpcException {
        final Object partnerId = 77;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { partnerId, "PARTNER-77" });

        when(concons.getPartnerId()).thenReturn(idDto);
        when(odoo.readFromModel(eq(odoo.RES_PARTNER), anyMap(), eq(partnerId))).thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            DestinazioneDTO.fromXMLRPC(odoo, concons);
        });
        assertThat(ex.getMessage()).isEqualTo("Non trovo informazioni della destinazione.");
    }

    // 2: concons == null -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenConsegnaContactIsNull() throws XmlRpcException {
        ContattoConsegnaDTO nullConcons = null;
        assertThrows(InconsistentDTOException.class, () -> {
            DestinazioneDTO.fromXMLRPC(odoo, nullConcons);
        });
    }

    // 3: concons present but partnerId num empty -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenPartnerIdMissing() throws XmlRpcException {
        // IdentifierDTO built from empty array to simulate missing num (getNum() -> Optional.empty())
        IdentifierDTO emptyIdDto = new IdentifierDTO(new Object[] {null, null}); 
        when(concons.getPartnerId()).thenReturn(emptyIdDto);

        assertThrows(InconsistentDTOException.class, () -> {
            DestinazioneDTO.fromXMLRPC(odoo, concons);
        });
    }
}