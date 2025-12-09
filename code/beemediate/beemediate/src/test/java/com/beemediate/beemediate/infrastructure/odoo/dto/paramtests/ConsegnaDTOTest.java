package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.springframework.boot.test.context.SpringBootTest;

import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

@SpringBootTest
@RunWith(Parameterized.class)
public class ConsegnaDTOTest {

	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String warehouseID = "warehouse_id";
		List<Object[]> tests = new ArrayList<>();
		
		//0 ID ok, warehouseID ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(warehouseID, new Object[] { 1 , "WH/001" } ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(warehouseID, new Object[] { Optional.of(1) , Optional.of("WH/001") } ); }},
							} );
		
		//1 ID notOk, warehouseID ok (id errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(warehouseID, new Object[] { "1" , "WH/001" } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(warehouseID, new Object[] { Optional.empty() , Optional.of("WH/001") } ); }},
							} );

		//2 ID null, warehouseID ok (name errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(warehouseID, new Object[] { 1 , 1 } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(warehouseID, new Object[] { Optional.of(1) , Optional.empty() } ); }},
							} );
		
		//3 ID ok, warehouseID notOk (null)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(warehouseID, null ); }},
				null
							} );

		
		//4 ID notOk, warehouseID notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(warehouseID, new Object[] { 1 } ); }},
				null
							} );

		
		
		return tests;
	}
	
	public ConsegnaDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
		final String ID = "id";
		final String warehouseID = "warehouse_id";
		ConsegnaDTO cons = null;
		try {
			cons = new ConsegnaDTO(in);
			assertThat(cons)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID));
			
			assertThat(cons.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(cons.getWarehouseId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, id -> {
				        assertThat(id.getNum()).isEqualTo( ( (Object[])  out.get(warehouseID))[0] );
				        assertThat(id.getName()).isEqualTo( ( (Object[])  out.get(warehouseID))[1] );
				    });
		}catch(Exception e) {
			/* warehouseID 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( in.get(warehouseID) )
					.matches(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
	
}
