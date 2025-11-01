package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.reset;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC
 * 
 * CASE| 		prv == null || prv.getPickingTypeId().getNum().isEmpty()		|		res.length == 0		| ESITO
 * 0   |			F			F												|			F				| happy path
 * 1   |			F			F												|			T				| EmptyFetchException ("Non trovo informazioni sulla consegna.")
 * 2   |			T			-												|			-				| InconsistentDTOException
 * 3   |			F			T												|			-				| InconsistentDTOException
 */
public class ConsegnaDTOXMLRPCTest {

    @Mock
    private OdooApiConfig odoo;

    @Mock
    private PreventivoDTO prv;

    @Before
    public void setup() {
        MockitoAnnotations.openMocks(this);
    }

    @After
    public void teardown() {
        reset(odoo, prv);
    }

    // 0: happy path -> readFromModel returns a non-empty array with a map
    @Test
    public void testFromXMLRPC_returnsConsegnaDTO_whenAllGood() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
        final Object pickingTypeId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "PICK-1" });

        Map<String, Object> map = new HashMap<>();
        map.put("id", 1);
        // warehouse_id is an identifier array expected by the constructor
        map.put("warehouse_id", new Object[] { 99, "WARE-99" });

        when(prv.getPickingTypeId()).thenReturn(idDto);
        // readFromModel is called with ("stock.picking.type", requestInfo, id)
        when(odoo.readFromModel(eq("stock.picking.type"), anyMap(), eq(pickingTypeId))).thenReturn(new Object[] { map });

        ConsegnaDTO expected = new ConsegnaDTO(map);
        ConsegnaDTO actual = ConsegnaDTO.fromXMLRPC(odoo, prv);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    // 1: readFromModel returns empty -> EmptyFetchException
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoResourceFound() throws XmlRpcException {
        final Object pickingTypeId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "PICK-1" });

        when(prv.getPickingTypeId()).thenReturn(idDto);
        when(odoo.readFromModel(eq("stock.picking.type"), anyMap(), eq(pickingTypeId))).thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            ConsegnaDTO.fromXMLRPC(odoo, prv);
        });
        assertThat(ex.getMessage()).isEqualTo("Non trovo informazioni sulla consegna.");
    }

    // 2: prv == null -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenPreventivoIsNull() throws XmlRpcException {
        PreventivoDTO nullPrv = null;
        assertThrows(InconsistentDTOException.class, () -> {
            ConsegnaDTO.fromXMLRPC(odoo, nullPrv);
        });
    }

    // 3: prv present but pickingTypeId num empty -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenPickingTypeIdMissing() throws XmlRpcException {
        // IdentifierDTO built from empty array to simulate missing num (getNum() -> Optional.empty())
        IdentifierDTO emptyIdDto = new IdentifierDTO(new Object[] { null, null}); 
        when(prv.getPickingTypeId()).thenReturn(emptyIdDto);

        assertThrows(InconsistentDTOException.class, () -> {
            ConsegnaDTO.fromXMLRPC(odoo, prv);
        });
    }
}