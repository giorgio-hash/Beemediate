package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoFornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/**
 * Metodo MCDC
     /**
     * Metodo MCDC
     * 
     * 
<table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>f==null</th>
            <th>f.getName().isEmpty()</th>
            <th>pr==null</th>
            <th>any p.sellerIds().isEmpty()</th>
            <th>ids.length==0</th>
            <th>res.length==0</th>
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
            <td>F</td>
            <td>F</td>
            <td style="text-align: left;">happy path</td>
        </tr>
        <tr>
            <td>1</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>2</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>3</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>4</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">InconsistentDTOException</td>
        </tr>
        <tr>
            <td>5</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td>-</td>
            <td style="text-align: left;">EmptyFetchException</td>
        </tr>
        <tr>
            <td>6</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td style="text-align: left;">EmptyFetchException</td>
        </tr>
    </tbody>
</table>
 */
public class ProdottoFornitoreDTOXMLRPCTest {

    /**
     * Metodo MCDC
     * 
     * 
  CASE	|		f==null		|	f.getName().isEmpty()	|	pr==null	|	any p.sellerIds().isEmpty()	|	ids.length==0	|	res.length==0		|ESITO
  	0	|			F				F							F				F								F					F				| happy path
  	1	|			T				-							-				-								-					-				| InconsistentDTOException
  	2	|			F				T							-				-								-					-				| InconsistentDTOException
  	3	|			F				F							T				-								-					-				| InconsistentDTOException
  	4	|			F				F							F				T								-					-				| InconsistentDTOException
  	5	|			F				F							F				F								T					-				| EmptyFetchException
  	6	|			F				F							F				F								F					T				| EmptyFetchException	
     */
	
    @Mock
    private OdooApiConfig odoo;

    @Mock
    private FornitoreDTO f;
    
    @Mock
    private ProdottoDTO pr;

    @Before
    public void setup() {
        MockitoAnnotations.openMocks(this);
    }
    
    
    @Test
    public void testRetrieveProdottoFornitoreDTO_Correctly_withMock () throws XmlRpcException, InconsistentDTOException, EmptyFetchException {

        // mock fornitore name
        when(f.getName()).thenReturn(Optional.of("GEALAN"));

        // prepare ProdottoDTO with sellerIds
        ProdottoDTO prod = org.mockito.Mockito.mock(ProdottoDTO.class);
        Object[] sellerIds = new Object[] { 1, 2, 3 };
        when(prod.getSellerIds()).thenReturn(Optional.of(sellerIds));

        ProdottoDTO[] prodotti = new ProdottoDTO[] { prod };

        // prepare supplierinfo records returned by readFromModel
        Map<String, Object> rec1 = new HashMap<>();
        rec1.put("id", 10);
        rec1.put("product_id", new Object[] { 1, "PROID" });
        rec1.put("partner_id", new Object[] { 2, "PRTNID" });
        rec1.put("product_uom_id", new Object[] { 3, "M" });

        Object[] results = new Object[] { rec1, rec1, rec1 };

        // IMPORTANT: mock searchFromModel with permissive matchers (don't try to eq() complex lists)
        when(odoo.searchFromModel(eq("product.supplierinfo"), anyMap(), anyList(), anyList()))
            .thenReturn(sellerIds);

        // mock readFromModel: the third arg is an Object[] in production, so match with any(Object[].class)
        when(odoo.readFromModel(eq("product.supplierinfo"), anyMap(), eq(sellerIds)))
            .thenReturn(results);

        // execute
        ProdottoFornitoreDTO[] actualArray = ProdottoFornitoreDTO.fromXMLRPC(odoo, prodotti, f);

        // expected (compare each produced DTO to the one built from rec1)
        ProdottoFornitoreDTO expected = new ProdottoFornitoreDTO(rec1);
        for (ProdottoFornitoreDTO actual : actualArray) {
            assertThat(actual)
                .isNotNull()
                .usingRecursiveComparison()
                .isEqualTo(expected);
        } 
    }
    
    
    @Test
    public void testInconsistentDTOException_whenFornitoreNull_withMock() {
    	f = null;
        assertThrows(InconsistentDTOException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { pr }, f);
        } );
    }
    
    
    @Test
    public void testInconsistentDTOException_whenFornitoreHasNoName_withMock() {
    	when(f.getName()).thenReturn(Optional.empty());
        assertThrows(InconsistentDTOException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { pr }, f);
        } );
    }
    
    @Test
    public void testInconsistentDTOException_whenProdottoIsNull_withMock() {
    	when(f.getName()).thenReturn(Optional.of("GEALAN"));
    	
        assertThrows(InconsistentDTOException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, null, f);
        } );
    }
    
    @Test
    public void testInconsistentDTOException_whenProdottoHasNoSellerIds_withMock() {
    	when(f.getName()).thenReturn(Optional.of("GEALAN"));
    	when(pr.getSellerIds()).thenReturn(Optional.empty());
        assertThrows(InconsistentDTOException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { pr }, f);
        } );
        
    	when(pr.getSellerIds()).thenReturn(Optional.of(new Object[0]));
        assertThrows(InconsistentDTOException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { pr }, f);
        } );
    }
    
    
    @Test
    public void testEmptyFetchException_whenNoIdFetched_withMock() throws XmlRpcException {
    
        // mock fornitore name
        when(f.getName()).thenReturn(Optional.of("GEALAN"));

        // prepare ProdottoDTO with sellerIds
        ProdottoDTO prod = org.mockito.Mockito.mock(ProdottoDTO.class);
        Object[] sellerIds = new Object[] { 1, 2, 3 };
        when(prod.getSellerIds()).thenReturn(Optional.of(sellerIds));

        // prepare supplierinfo records returned by readFromModel
        Map<String, Object> rec1 = new HashMap<>();
        rec1.put("id", 10);
        rec1.put("product_id", new Object[] { 1, "PROID" });
        rec1.put("partner_id", new Object[] { 2, "PRTNID" });
        rec1.put("product_uom_id", new Object[] { 3, "M" });

        // IMPORTANT: mock searchFromModel with permissive matchers (don't try to eq() complex lists)
        when(odoo.searchFromModel(eq("product.supplierinfo"), anyMap(), anyList(), anyList()))
            .thenReturn(new Object[0]);
        
        assertThrows(EmptyFetchException.class, () -> {
            @SuppressWarnings("unused")
			ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { prod }, f);
        } );
    }
    
    @Test
    public void testEmptyFetchException_whenIdFetched_butNoResourceFound_withMock() throws XmlRpcException {
 

        // mock fornitore name
        when(f.getName()).thenReturn(Optional.of("GEALAN"));

        // prepare ProdottoDTO with sellerIds
        ProdottoDTO pr = org.mockito.Mockito.mock(ProdottoDTO.class);
        Object[] sellerIds = new Object[] { 1, 2, 3 };
        when(pr.getSellerIds()).thenReturn(Optional.of(sellerIds));

        // prepare supplierinfo records returned by readFromModel
        Map<String, Object> rec1 = new HashMap<>();
        rec1.put("id", 10);
        rec1.put("product_id", new Object[] { 1, "PROID" });
        rec1.put("partner_id", new Object[] { 2, "PRTNID" });
        rec1.put("product_uom_id", new Object[] { 3, "M" });

        // IMPORTANT: mock searchFromModel with permissive matchers (don't try to eq() complex lists)
        when(odoo.searchFromModel(eq("product.supplierinfo"), anyMap(), anyList(), anyList()))
            .thenReturn(sellerIds);

        // mock readFromModel: the third arg is an Object[] in production, so match with any(Object[].class)
        when(odoo.readFromModel(eq("product.supplierinfo"), anyMap(), eq(sellerIds)))
            .thenReturn(new Object[0]);
        
        assertThrows(EmptyFetchException.class, () -> {
            ProdottoFornitoreDTO[] prf = ProdottoFornitoreDTO.fromXMLRPC(odoo, new ProdottoDTO[] { pr }, f);
        } );
    }
}