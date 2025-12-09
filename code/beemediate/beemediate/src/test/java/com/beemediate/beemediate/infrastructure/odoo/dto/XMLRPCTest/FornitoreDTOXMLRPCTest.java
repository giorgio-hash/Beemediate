package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;


import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.anyString;
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
import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;

/**
 * Metodo MCDC
 * 
 * 
<table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>f == null</th>
            <th>f.getName().isEmpty()</th>
            <th>ids.length == 0</th>
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
            <td>F</td>
            <td style="text-align: left;">happy path</td>
        </tr>
        <tr>
            <td>1</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td style="text-align: left;">EmptyFetchException ("Non trovo GEALAN")</td>
        </tr>
        <tr>
            <td>2</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td style="text-align: left;">EmptyFetchException ("Trovato GEALAN, ma non riesco ad estrarlo.")</td>
        </tr>
        <tr>
            <td>3</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>4</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
    </tbody>
</table>
 */
public class FornitoreDTOXMLRPCTest {

    /**
 * Metodo MCDC
 * 
 * 
 CASE| 		f == null || f.getName().isEmpty()		|		ids.length == 0			|		res.length == 0		| ESITO
    0| 			F			F						|			F					|			F				| happy path
    1| 			F			F						|			T					|			-				| EmptyFetchException ("Non trovo GEALAN")
    2| 			F			F						|			F					|			T				| EmptyFetchException ("Trovato GEALAN, ma non riesco ad estrarlo.")
    3| 			T			-						|			-					|			-				| InconsistentDTOException
    4| 			F			T						|			-					|			-				| InconsistentDTOException
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

    // 0: happy path -> searchFromModel returns ids non-empty and readFromModel returns a map
    @Test
    public void testFromXMLRPC_returnsFornitoreDTO_whenAllGood() throws XmlRpcException, EmptyFetchException {
        Object[] ids = new Object[] { 1 };
        Map<String, Object> map = new HashMap<>();
        map.put("id", 1);
        map.put("name", "GEALAN");
        map.put("ref", "COD-01");

        // searchFromModel called with (odoo.RES_PARTNER, requestInfo, Arrays.asList("name","=","GEALAN"))
        when(odoo.searchFromModel(anyString(), anyMap(), anyList())).thenReturn(ids);
        // readFromModel called with (odoo.RES_PARTNER, requestInfo, ids)
        when(odoo.readFromModel(anyString(), anyMap(), any(Object[].class))).thenReturn(new Object[] { map });

        FornitoreDTO expected = new FornitoreDTO(map);
        FornitoreDTO actual = FornitoreDTO.fromXMLRPC(odoo);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    // 1: searchFromModel returns empty -> EmptyFetchException "Non trovo GEALAN"
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoIdsFound() throws XmlRpcException {
        Object[] emptyIds = new Object[0];

        when(odoo.searchFromModel(anyString(), anyMap(), anyList())).thenReturn(emptyIds);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            FornitoreDTO.fromXMLRPC(odoo);
        });
        assertThat(ex.getMessage()).isEqualTo("Non trovo GEALAN");
    }

    // 2: searchFromModel returns ids but readFromModel returns empty -> EmptyFetchException "Trovato GEALAN, ma non riesco ad estrarlo."
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenReadReturnsEmpty() throws XmlRpcException {
        Object[] ids = new Object[] { 1 };

        when(odoo.searchFromModel(anyString(), anyMap(), anyList())).thenReturn(ids);
        when(odoo.readFromModel(anyString(), anyMap(), any(Object[].class))).thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            FornitoreDTO.fromXMLRPC(odoo);
        });
        assertThat(ex.getMessage()).isEqualTo("Trovato GEALAN, ma non riesco ad estrarlo.");
    }
}