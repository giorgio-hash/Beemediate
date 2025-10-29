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

@RunWith(Parameterized.class)
public class DestinazioneDTOTest {
	
	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String codiceDestinazione = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(codiceDestinazione, "2"); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(codiceDestinazione, Optional.of("2")); }},
							} );
		
		// id notOk, ref null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(codiceDestinazione, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(codiceDestinazione, Optional.empty()); }},
							} );
		
		// id null, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(codiceDestinazione, 2); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(codiceDestinazione, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
	public DestinazioneDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
		final String ID = "id";
		final String codiceDestinazione = "ref";
		DestinazioneDTO dest = null;
		
			dest = new DestinazioneDTO(in);
			assertThat(dest)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("codiceDestinazione", out.get(codiceDestinazione));
			
			assertThat(dest.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			assertThat(dest.getCodiceDestinazione())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(codiceDestinazione));
			});
	}

}
