package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.reset;
import static org.mockito.Mockito.when;

import java.util.HashMap;
import java.util.Map;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.ArticoloPreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC per ProdottoDTO.fromXMLRPC.
 * 
 * 
 <table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>ap == null</th>
            <th>any ap[i].getProductId().getNum().isEmpty()</th>
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
            <td style="text-align: left;">EmptyFetchException ("Non è stato possibile trovare alcun prodotto associato agli articoli: " + sb.toString())</td>
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
public class ProdottoDTOXMLRPCTest {

    /**
     * MCDC
 * CASE| 		ap == null  | any ap[i].getProductId().getNum().isEmpty()		|		res.length == 0		| ESITO
 * 0   |			F		|	F												|			F				| happy path
 * 1   |			F		|	F												|			T				| EmptyFetchException ("Non è stato possibile trovare alcun prodotto associato agli articoli: " + sb.toString())
 * 2   |			T		|	-												|			-				| InconsistentDTOException
 * 3   |			F		|	T												|			-				| InconsistentDTOException
 */
    @Mock
    private OdooApiConfig odoo;

    @Before
    public void setup() {
        MockitoAnnotations.openMocks(this);
    }

    @After
    public void teardown() {
        reset(odoo);
    }

    // 0: happy path -> readFromModel returns non-empty array of maps
    @Test
    public void testFromXMLRPC_returnsProdottoDTOArray_whenAllGood() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
        // prepare two ArticoloPreventivoDTO entries with product ids
        Map<String, Object> a1 = new HashMap<>();
        a1.put("id", 101);
        a1.put("order_id", new Object[] { 10, "PO-10" });
        a1.put("product_id", new Object[] { 1001, "PROD-1001" });
        a1.put("product_qty", 2.0d);

        Map<String, Object> a2 = new HashMap<>();
        a2.put("id", 102);
        a2.put("order_id", new Object[] { 11, "PO-11" });
        a2.put("product_id", new Object[] { 1002, "PROD-1002" });
        a2.put("product_qty", 3.0d);

        ArticoloPreventivoDTO ap1 = new ArticoloPreventivoDTO(a1);
        ArticoloPreventivoDTO ap2 = new ArticoloPreventivoDTO(a2);

        ArticoloPreventivoDTO[] apArray = new ArticoloPreventivoDTO[] { ap1, ap2 };

        // prepare product.product read results (seller_ids field)
        Map<String, Object> p1 = new HashMap<>();
        p1.put("id", 1001);
        p1.put("seller_ids", new Object[] {});

        Map<String, Object> p2 = new HashMap<>();
        p2.put("id", 1002);
        p2.put("seller_ids", new Object[] {});

        // mock readFromModel for product.product -> return p1,p2
        when(odoo.readFromModel(eq("product.product"), anyMap(), any(Object[].class)))
            .thenReturn(new Object[] { p1, p2 });

        ProdottoDTO[] expected = new ProdottoDTO[] { new ProdottoDTO(p1), new ProdottoDTO(p2) };
        ProdottoDTO[] actual = ProdottoDTO.fromXMLRPC(odoo, apArray);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    // 1: readFromModel returns empty -> EmptyFetchException
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoProductsFound() throws XmlRpcException {
        Map<String, Object> a1 = new HashMap<>();
        a1.put("id", 101);
        a1.put("order_id", new Object[] {null, null} );
        a1.put("product_id", new Object[] { 1001, "PROD-1001" });

        ArticoloPreventivoDTO ap1 = new ArticoloPreventivoDTO(a1);
        ArticoloPreventivoDTO[] apArray = new ArticoloPreventivoDTO[] { ap1 };

        when(odoo.readFromModel(eq("product.product"), anyMap(), any(Object[].class)))
            .thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            ProdottoDTO.fromXMLRPC(odoo, apArray);
        });
        // message contains prefix used in code; we check it starts with expected phrase
        assertThat(ex.getMessage()).startsWith("Non è stato possibile trovare alcun prodotto associato agli articoli:");
    }

    // 2: ap == null -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenApIsNull() {
        ArticoloPreventivoDTO[] apArray = null;
        assertThrows(InconsistentDTOException.class, () -> {
            ProdottoDTO.fromXMLRPC(odoo, apArray);
        });
    }

    // 3: one ArticoloPreventivoDTO has missing product id -> InconsistentDTOException
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenProductIdMissingInArticle() {
        Map<String, Object> a1 = new HashMap<>();
        a1.put("id", 101);
        a1.put("order_id", new Object[] {null, null} );
        a1.put("product_id", new Object[] {null, null} );
        // product_id missing to simulate missing num

        ArticoloPreventivoDTO ap1 = new ArticoloPreventivoDTO(a1);
        ArticoloPreventivoDTO[] apArray = new ArticoloPreventivoDTO[] { ap1 };

        assertThrows(InconsistentDTOException.class, () -> {
            ProdottoDTO.fromXMLRPC(odoo, apArray);
        });
    }
}