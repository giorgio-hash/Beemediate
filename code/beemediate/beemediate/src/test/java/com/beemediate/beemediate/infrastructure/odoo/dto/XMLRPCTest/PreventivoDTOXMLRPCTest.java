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