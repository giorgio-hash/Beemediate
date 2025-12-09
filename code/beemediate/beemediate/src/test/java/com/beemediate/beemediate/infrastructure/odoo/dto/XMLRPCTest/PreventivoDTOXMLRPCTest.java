package com.beemediate.beemediate.infrastructure.odoo.dto.XMLRPCTest;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertThrows;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyMap;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.when;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.Test;
import org.junit.jupiter.api.BeforeEach;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;


/**
 * Metodo MCDC
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
            <td style="text-align: left;">EmptyFetchException ("Nessun preventivo "new" per GEALAN")</td>
        </tr>
        <tr>
            <td>2</td>
            <td>F</td>
            <td>F</td>
            <td>F</td>
            <td>T</td>
            <td style="text-align: left;">EmptyFetchException ("Trovato preventivi per GEALAN, ma nessuno estratto.")</td>
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
public class PreventivoDTOXMLRPCTest {

    /**
     * Metodo MCDC
     * 
     * 
  CASE| 		f == null || f.getName().isEmpty()		|		ids.length == 0			|		res.length == 0		| ESITO
     0| 			F			F						|			F					|			F				| happy path
     1| 			F			F						|			T					|			-				| EmptyFetchException ("Nessun preventivo \"new\" per GEALAN")
     2| 			F			F						|			F					|			T				| EmptyFetchException ("Trovato preventivi per GEALAN, ma nessuno estratto.")
     3| 			T			-						|			-					|			-				| InconsistentDTOException
     4| 			F			T						|			-					|			-				| InconsistentDTOException
     */
    
	@Mock
	private OdooApiConfig odoo;
	
	@Mock
	private FornitoreDTO f;

	  
	@BeforeEach
	public void setup() {
			MockitoAnnotations.openMocks(this);
	}
	
	//0
	@Test
	public void testRetrievePreventivoDTO_Correctly_withMock() throws XmlRpcException, EmptyFetchException, InconsistentDTOException {
		
      odoo = org.mockito.Mockito.mock(OdooApiConfig.class);
      f = org.mockito.Mockito.mock(FornitoreDTO.class);
		
      	List<Object> partnerGEALANcond = new ArrayList<>();
      	partnerGEALANcond.add("partner_id");partnerGEALANcond.add("=");partnerGEALANcond.add("GEALAN");
		Object[] id = new Object[] { 1 };
		Map<String, Object> res = new HashMap() {{
			put("id",1);
			put("name","NOME");
			put("partner_id", new Object[] {1, "PARTNID-01"} );
			put("product_id", new Object[] {1, "PRODUCID-9"} );
			put("currency_id", new Object[] {1, "EUR"} );
			put("picking_type_id", new Object[] {1, "DELVHLOC_WH"});
			put("company_id", new Object[] {1, "SERRAMENTI"});
			put("origin", "S001/P002");
			put("order_line", new Object[] { 1, 2, 3, 4});
			put("date_order",null);
			put("date_approve",null);
			put("date_planned",null);
			
		}};
		
		when(f.getName()).thenReturn(Optional.of("GEALAN"));
		when(odoo.searchFromModel(eq("purchase.order"), anyMap(), eq(partnerGEALANcond), anyList())).thenReturn(id);
		when(odoo.readFromModel(eq("purchase.order"), anyMap(), eq(id))).thenReturn(new Object[] { res });
		
		PreventivoDTO expected = new PreventivoDTO(res);
		PreventivoDTO actual = PreventivoDTO.fromXMLRPC(odoo, f);
		
      assertThat(actual)
         .isNotNull()
         .usingRecursiveComparison()
         .isEqualTo(expected);
	}
	
	//1
	@Test
	public void testNoIdFetched_withMock() throws XmlRpcException {
	
	      odoo = org.mockito.Mockito.mock(OdooApiConfig.class);
	      f = org.mockito.Mockito.mock(FornitoreDTO.class);
			
	      	List<Object> partnerGEALANcond = new ArrayList<>();
	      	partnerGEALANcond.add("partner_id");partnerGEALANcond.add("=");partnerGEALANcond.add("GEALAN");
	      	Object[] id = new Object[0];
	
			when(f.getName()).thenReturn(Optional.of("GEALAN"));
			when(odoo.searchFromModel(eq("purchase.order"), anyMap(), eq(partnerGEALANcond), anyList())).thenReturn(id);
			
			EmptyFetchException exception = assertThrows(EmptyFetchException.class, () -> {
				PreventivoDTO.fromXMLRPC(odoo, f);
			});
			assertThat(exception.getMessage()).isEqualTo("Nessun preventivo \"new\" per GEALAN");
	}
	
	//2
	@Test
	public void testIdFetchediDSuccessfully_butNoResourceFound_withMock() throws XmlRpcException {
		
	      odoo = org.mockito.Mockito.mock(OdooApiConfig.class);
	      f = org.mockito.Mockito.mock(FornitoreDTO.class);
			
	      	List<Object> partnerGEALANcond = new ArrayList<>();
	      	partnerGEALANcond.add("partner_id");partnerGEALANcond.add("=");partnerGEALANcond.add("GEALAN");
			Object[] id = new Object[] { 1 };
			
			when(f.getName()).thenReturn(Optional.of("GEALAN"));
			when(odoo.searchFromModel(eq("purchase.order"), anyMap(), eq(partnerGEALANcond), anyList())).thenReturn(id);
			when(odoo.readFromModel(eq("purchase.order"), anyMap(), eq(id))).thenReturn(new Object[0]);
			
			EmptyFetchException exception = assertThrows(EmptyFetchException.class, () -> {
				PreventivoDTO.fromXMLRPC(odoo, f);
			});
			assertThat(exception.getMessage()).isEqualTo("Trovato preventivi per GEALAN, ma nessuno estratto.");
	}
	
	//3
	@Test
	public void testFornitoreNull() {
		
	      odoo = org.mockito.Mockito.mock(OdooApiConfig.class);
	      f = null;
	      
		assertThrows(InconsistentDTOException.class, () -> {
			PreventivoDTO.fromXMLRPC(odoo, f);
		});
	}
	
	//4
	@Test
	public void testFornitoreHasNoName() {
		
	      odoo = org.mockito.Mockito.mock(OdooApiConfig.class);
	      f = org.mockito.Mockito.mock(FornitoreDTO.class);
	      when(f.getName()).thenReturn(Optional.empty());
	      
		assertThrows(InconsistentDTOException.class, () -> {
			PreventivoDTO.fromXMLRPC(odoo, f);
		});
	}
}