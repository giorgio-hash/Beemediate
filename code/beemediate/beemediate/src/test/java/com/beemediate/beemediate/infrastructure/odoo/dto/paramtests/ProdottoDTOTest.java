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

import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;

@SpringBootTest
@RunWith(Parameterized.class)
public class ProdottoDTOTest {
	
	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String sellerIds = "seller_ids";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(sellerIds, new Object[] { "2" }  ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(sellerIds, Optional.of( new Object[] { "2" } )); }},
							} );
		
		// id notOk, ref null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(sellerIds, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(sellerIds, Optional.empty()); }},
							} );
		
		// id null, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(sellerIds, "2" ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(sellerIds, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
	public ProdottoDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
		final String ID = "id";
		final String sellerIds = "seller_ids";
		ProdottoDTO prod = null;
		
			prod = new ProdottoDTO(in);
			assertThat(prod)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID));
			
			assertThat(prod.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			if(prod.getSellerIds().isPresent()) {
				Optional<Object[]> actual = prod.getSellerIds();
				Optional<Object[]> expected = (Optional<Object[]>)  out.get(sellerIds);
				assertThat(actual.get())
						.contains(expected.get());
			}else
				assertThat(prod.getSellerIds()).isEmpty();
	}

}
