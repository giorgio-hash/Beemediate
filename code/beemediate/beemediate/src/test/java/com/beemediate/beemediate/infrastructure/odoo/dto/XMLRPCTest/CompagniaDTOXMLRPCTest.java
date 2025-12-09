package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;
import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.anyString;
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
import com.beemediate.beemediate.infrastructure.odoo.dto.CompagniaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC
 <table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>prv == null</th>
            <th>prv.getCompanyId().getNum().isEmpty()</th>
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
            <td style="text-align: left;">EmptyFetchException ("Non trovo informazioni della compagnia ")</td>
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
public class CompagniaDTOXMLRPCTest {

    /**
     *  
 * CASE| 		prv == null || prv.getCompanyId().getNum().isEmpty()		|		res.length == 0		| ESITO
 * 0   |			F			F											|			F				| happy path
 * 1   |			F			F											|			T				| EmptyFetchException ("Non trovo informazioni della compagnia ")
 * 2   |			T			-											|			-				| InconsistentDTOException
 * 3   |			F			T											|			-				| InconsistentDTOException
     */
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

    /**
     * 0: happy path -> readFromModel returns a non-empty array with a map
     * @throws XmlRpcException
     * @throws EmptyFetchException
     * @throws InconsistentDTOException
     */
    @Test
    public void testFromXMLRPC_returnsCompagniaDTO_whenAllGood() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
        // prepare mocks
        final Object companyId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "COMPANY-1" });

        Map<String, Object> map = new HashMap<>();
        map.put("id", 1);
        map.put("ref", "REG-123");

        when(prv.getCompanyId()).thenReturn(idDto);
        // readFromModel is called with (odoo.RES_PARTNER, requestInfo, id) where id is an Object (Integer)
        when(odoo.readFromModel(anyString(), anyMap(), eq(companyId))).thenReturn(new Object[] { map });

        CompagniaDTO expected = new CompagniaDTO(map);
        CompagniaDTO actual = CompagniaDTO.fromXMLRPC(odoo, prv);

        assertThat(actual)
            .isNotNull()
            .usingRecursiveComparison()
            .isEqualTo(expected);
    }

    /**
     * 1: readFromModel returns empty -> EmptyFetchException
     * @throws XmlRpcException
     */
    @Test
    public void testFromXMLRPC_throwsEmptyFetch_whenNoResourceFound() throws XmlRpcException {
        final Object companyId = 1;
        IdentifierDTO idDto = new IdentifierDTO(new Object[] { 1, "COMPANY-1" });

        when(prv.getCompanyId()).thenReturn(idDto);
        when(odoo.readFromModel(anyString(), anyMap(), eq(companyId))).thenReturn(new Object[0]);

        EmptyFetchException ex = assertThrows(EmptyFetchException.class, () -> {
            CompagniaDTO.fromXMLRPC(odoo, prv);
        });
        assertThat(ex.getMessage()).isEqualTo("Non trovo informazioni della compagnia ");
    }

    /**
     * 2: prv == null -> InconsistentDTOException
     */
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenPreventivoIsNull() {
        PreventivoDTO nullPrv = null;
        assertThrows(InconsistentDTOException.class, () -> {
            CompagniaDTO.fromXMLRPC(odoo, nullPrv);
        });
    }

    /**
     * 3: prv present but companyId num empty -> InconsistentDTOException
     */
    @Test
    public void testFromXMLRPC_throwsInconsistent_whenCompanyIdMissing() {
        // IdentifierDTO built from null/empty array to simulate missing num
        IdentifierDTO emptyIdDto = new IdentifierDTO(new Object[] { null, null}); // getNum() will be Optional.empty()
        when(prv.getCompanyId()).thenReturn(emptyIdDto);

        assertThrows(InconsistentDTOException.class, () -> {
            CompagniaDTO.fromXMLRPC(odoo, prv);
        });
    }

}