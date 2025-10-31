package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.assertj.core.util.Arrays;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.springframework.boot.test.context.SpringBootTest;

import com.beemediate.beemediate.infrastructure.odoo.dto.CompagniaDTO;

@SpringBootTest
@RunWith(Parameterized.class)
public class CompagniaDTOTest {
	
	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String companyRegistry = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(companyRegistry, "2"); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(companyRegistry, Optional.of("2")); }},
							} );
		
		// id notOk, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(companyRegistry, "2"); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(companyRegistry, Optional.of("2")); }},
							} );
		
		// id ok, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(companyRegistry, 2); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(companyRegistry, Optional.empty()); }},
							} );
		
		// id notOk, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(companyRegistry, 2); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(companyRegistry, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
	public CompagniaDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
		final String ID = "id";
		final String companyRegistry = "ref";
		CompagniaDTO comp = null;
		
			comp = new CompagniaDTO(in);
			assertThat(comp)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("companyRegistry", out.get(companyRegistry));
			
			assertThat(comp.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(comp.getCompanyRegistry())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, id -> {
				assertEquals(id, out.get(companyRegistry));
			});
	}

}
