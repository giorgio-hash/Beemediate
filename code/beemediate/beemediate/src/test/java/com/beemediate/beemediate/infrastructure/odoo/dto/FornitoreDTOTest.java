package com.beemediate.beemediate.infrastructure.odoo.dto;

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

@SpringBootTest
@RunWith(Parameterized.class)
public class FornitoreDTOTest {
	
	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String nome = "name";
		final String codiceAzienda = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		/*
		 * 
		 * Voglio che i parametri ricevano input: ok, notOk, null.
		 * I parametri sono scorrelati tra loro.
		 * 
		CASE		id			name			ref
			0											<--escludo perchè ridondante
			1		notOk								<--escludo perchè ridondante
			2					notOK					<--escludo perchè ridondante
			3		null		notOk			
			4									notOk   <--escludo perchè ridondante
			5		notOK						null
			6					null			notOk	
			7		notOK		notOk			notOK	<--escludo perchè ridondante
		 * */
		
		//3
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(nome, 2); 			put(codiceAzienda, "2"); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(nome, Optional.empty()); put(codiceAzienda, Optional.of("2")); }},
							} );
		//5
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(nome, "2"); 			put(codiceAzienda, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(nome, Optional.of("2")); put(codiceAzienda, Optional.empty()); }},
							} );
		//6
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(nome, null); 			put(codiceAzienda, 2); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(nome, Optional.empty()); put(codiceAzienda, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
	public FornitoreDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
		final String ID = "id";
		final String nome="name";
		final String codiceAzienda = "ref";
		FornitoreDTO forn = null;
		
			forn = new FornitoreDTO(in);
			assertThat(forn)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("codiceAzienda", out.get(codiceAzienda))
				.hasFieldOrPropertyWithValue("name", out.get(nome));
			
			assertThat(forn.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			assertThat(forn.getCodiceAzienda())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(codiceAzienda));
			});
			
			assertThat(forn.getName())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(nome));
			});
	}

}
