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
import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC per ContattoConsegnaDTO.fromXMLRPC
 * 
<table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>cns == null</th>
            <th>cns.getWarehouseId().getNum().isEmpty()</th>
            <th>res.length == 0</th>
            <th>ESITO</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>0</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td style="text-align: left;">happy path</td>
        </tr>
        <tr>
            <td>1</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td style="text-align: left;">EmptyFetchException ("Non trovo informazioni del contatto di consegna.")</td>
        </tr>
        <tr>
            <td>2</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>3</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
    </tbody>
</table>
 */
public class ConConDTOXMLRPCTest {

    /**
 * Metodo MCDC
 * 
 * CASE| 		cns == null || cns.getWarehouseId().getNum().isEmpty()		|		res.length == 0		| ESITO
 * 0   |			F			F												|			F				| happy path
 * 1   |			F			F												|			T				| EmptyFetchException ("Non trovo informazioni del contatto di consegna.")
 * 2   |			T			-												|			-				| InconsistentDTOException
 * 3   |			F			T												|			-				| InconsistentDTOException
 */

    @Mock
    private OdooApiConfig odoo;

    @Mock
    private ConsegnaDTO cns;

    @Before
    public void setup() {
        MockitoAnnotations.openMocks(this);
    }

    @After
    public void teardown() {
        reset(odoo, cns);
    }

    // 0: happy path -> readFromModel returns a non-empty array with a map
    @Test
    public void testFromXMLRPC_returnsContattoConsegnaDTO_whenAllGood() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
        final Object warehouseId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "WH-1" });

        Map<String, Object> map = new HashMap<>();
        map.put("id", 1);
        map.put("partner_id", new Object[] { 77, "PARTNER-77" });

        when(cns.getWarehouseId()).thenReturn(idDto);
        // readFromModel is called with ("stock.warehouse", requestInfo, id)
        when(odoo.readFromModel(eq("stock.warehouse"), anyMap(), eq(warehouseId))).thenReturn(new Object[] { map });

        ContattoConsegnaDTO expected = new ContattoConsegnaDTO(map);
        ContattoConsegnaDTO actual = ContattoConsegnaDTO.fromXMLRPC(odoo, cns);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    // 1: readFromModel returns empty -> EmptyFetchException
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoResourceFound() throws XmlRpcException {
        final Object warehouseId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "WH-1" });

        when(cns.getWarehouseId()).thenReturn(idDto);
        when(odoo.readFromModel(eq("stock.warehouse"), anyMap(), eq(warehouseId))).thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            ContattoConsegnaDTO.fromXMLRPC(odoo, cns);
        });
        assertThat(ex.getMessage()).isEqualTo("Non trovo informazioni del contatto di consegna.");
    }

    // 2: cns == null -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenConsegnaIsNull() {
        ConsegnaDTO nullCns = null;
        assertThrows(InconsistentDTOException.class, () -> {
            ContattoConsegnaDTO.fromXMLRPC(odoo, nullCns);
        });
    }

    // 3: cns present but warehouseId num empty -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenWarehouseIdMissing() {
        // IdentifierDTO built from empty array to simulate missing num (getNum() -> Optional.empty())
        IdentifierDTO emptyIdDto = new IdentifierDTO(new Object[] {null, null}); 
        when(cns.getWarehouseId()).thenReturn(emptyIdDto);

        assertThrows(InconsistentDTOException.class, () -> {
            ContattoConsegnaDTO.fromXMLRPC(odoo, cns);
        });
    }
}