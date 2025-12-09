package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.ArticoloPreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Test suite MCDC per ArticoloPreventivoDTO.fromXMLRPC
 <table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASO</th>
            <th>prv == null</th>
            <th>prv.getOrderLine().isEmpty()</th>
            <th>ids.length == 0</th>
            <th>res.length == 0</th>
            <th>ESITO</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>A</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>B</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>C</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td style="text-align: left;">EmptyFetchException</td>
        </tr>
        <tr>
            <td>D</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td style="text-align: left;">EmptyFetchException</td>
        </tr>
        <tr>
            <td>E</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td style="text-align: left;">successo (mapping)</td>
        </tr>
        <tr>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td style="text-align: left;">successo (mapping multiplo)</td>
        </tr>
    </tbody>
</table>
 * Questi casi permettono di esercitare ogni condizione in modo indipendente
 * (ad esempio per la decisione 1, proviamo la condizione prv==null e la condizione
 * getOrderLine().isEmpty() separatamente).
 */
@ExtendWith(MockitoExtension.class)
public class ArtPrDTOXMLRPCTest {

    @Mock
    private OdooApiConfig odoo;

    /** Caso A: prv == null -> InconsistentDTOException*/ 
    @Test
    void mcdc_prvNull_throwsInconsistent() {
        assertThrows(InconsistentDTOException.class, () -> {
            ArticoloPreventivoDTO.fromXMLRPC(odoo, null);
        });
    }

    /**Caso B: prv non null ma getOrderLine() == Optional.empty() -> InconsistentDTOException */
    @Test
    void mcdc_orderLineEmpty_throwsInconsistent() {
        PreventivoDTO prv = mock(PreventivoDTO.class);
        when(prv.getOrderLine()).thenReturn(Optional.empty());

        assertThrows(InconsistentDTOException.class, () -> {
            ArticoloPreventivoDTO.fromXMLRPC(odoo, prv);
        });
    }

    /**
     * Caso C: getOrderLine() presente ma ids.length == 0 -> EmptyFetchException
     */
    @Test
    void mcdc_idsLengthZero_throwsEmptyFetch() {
        PreventivoDTO prv = mock(PreventivoDTO.class);
        Object[] idsEmpty = new Object[0];
        when(prv.getOrderLine()).thenReturn(Optional.of(idsEmpty));

        assertThrows(EmptyFetchException.class, () -> {
            ArticoloPreventivoDTO.fromXMLRPC(odoo, prv);
        });
    }

    /**
     * Caso D: ids presenti ma readFromModel ritorna array vuoto -> EmptyFetchException
     * @throws XmlRpcException
     */
    @Test
    void mcdc_readReturnsEmpty_throwsEmptyFetch() throws XmlRpcException {
        PreventivoDTO prv = mock(PreventivoDTO.class);
        Object[] ids = new Object[] { 42 };
        when(prv.getOrderLine()).thenReturn(Optional.of(ids));

        // stub: odoo.readFromModel ritorna array vuoto
        Object[] emptyRes = new Object[0];
        when(odoo.readFromModel(eq("purchase.order.line"), anyMap(), eq(ids))).thenReturn(emptyRes);

        assertThrows(EmptyFetchException.class, () -> {
            ArticoloPreventivoDTO.fromXMLRPC(odoo, prv);
        });

        verify(odoo, atLeastOnce()).readFromModel(eq("purchase.order.line"), anyMap(), eq(ids));
    }

    /**
     * Caso E: ids presenti e readFromModel ritorna 1 riga -> successo e mapping corretto
     * @throws Exception
     */
    @Test
    void mcdc_singleRow_successfulMapping() throws Exception {
        PreventivoDTO prv = mock(PreventivoDTO.class);
        Object[] ids = new Object[] { 101 };
        when(prv.getOrderLine()).thenReturn(Optional.of(ids));

        Map<String, Object> row = new HashMap<>();
        row.put("id", 555);
        row.put("order_id", new Object[] { 10, "PO-10" });
        row.put("product_id", new Object[] { 20, "PRODUCT-20" });
        row.put("product_qty", 12.5d);

        Object[] res = new Object[] { row };

        when(odoo.readFromModel(eq("purchase.order.line"), anyMap(), eq(ids))).thenReturn(res);

        ArticoloPreventivoDTO[] result = ArticoloPreventivoDTO.fromXMLRPC(odoo, prv);

        assertNotNull(result);
        assertEquals(1, result.length);

        ArticoloPreventivoDTO a = result[0];
        assertTrue(a.getId().isPresent());
        assertEquals(555, a.getId().get().intValue());

        assertNotNull(a.getOrderId());
        assertTrue(a.getOrderId().getNum().isPresent());
        assertEquals(10, a.getOrderId().getNum().get().intValue());
        assertTrue(a.getOrderId().getName().isPresent());
        assertEquals("PO-10", a.getOrderId().getName().get());

        assertNotNull(a.getProductId());
        assertTrue(a.getProductId().getNum().isPresent());
        assertEquals(20, a.getProductId().getNum().get().intValue());
        assertTrue(a.getProductId().getName().isPresent());
        assertEquals("PRODUCT-20", a.getProductId().getName().get());

        assertTrue(a.getProductQty().isPresent());
        assertEquals(12.5d, a.getProductQty().get());

        verify(odoo, atLeastOnce()).readFromModel(eq("purchase.order.line"), anyMap(), eq(ids));
    }

    /**
     * Caso F: ids presenti e readFromModel ritorna più righe -> successo mapping multiplo
     * @throws Exception
     */
    @Test
    void mcdc_multipleRows_successfulMapping() throws Exception {
        PreventivoDTO prv = mock(PreventivoDTO.class);
        Object[] ids = new Object[] { 200, 201 };
        when(prv.getOrderLine()).thenReturn(Optional.of(ids));

        Map<String, Object> row1 = new HashMap<>();
        row1.put("id", 1);
        row1.put("order_id", new Object[] { 500, "PO-500" });
        row1.put("product_id", new Object[] { 600, "PROD-600" });
        row1.put("product_qty", 3.0d);

        Map<String, Object> row2 = new HashMap<>();
        row2.put("id", 2);
        row2.put("order_id", new Object[] { 501, "PO-501" });
        row2.put("product_id", new Object[] { 601, "PROD-601" });
        row2.put("product_qty", 7.0d);

        Object[] res = new Object[] { row1, row2 };

        when(odoo.readFromModel(eq("purchase.order.line"), anyMap(), eq(ids))).thenReturn(res);

        ArticoloPreventivoDTO[] result = ArticoloPreventivoDTO.fromXMLRPC(odoo, prv);

        assertNotNull(result);
        assertEquals(2, result.length);

        assertEquals(1, result[0].getId().get().intValue());
        assertEquals(2, result[1].getId().get().intValue());

        assertEquals(3.0d, result[0].getProductQty().get());
        assertEquals(7.0d, result[1].getProductQty().get());

        verify(odoo, atLeastOnce()).readFromModel(eq("purchase.order.line"), anyMap(), eq(ids));
    }
}