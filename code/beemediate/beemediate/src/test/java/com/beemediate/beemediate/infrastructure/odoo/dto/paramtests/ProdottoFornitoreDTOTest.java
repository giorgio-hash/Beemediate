package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;

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

import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoFornitoreDTO;

@SpringBootTest
@RunWith(Parameterized.class)
public class ProdottoFornitoreDTOTest {
	
	
	private Map<String, Object> in;
	private Map<String, Object> out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		/*
	CASO	 		id				productId		sequence		productName		productCode		partnerId		productUomId	|	ESITO
		0																															|	ok
		1							null																							|	eccezione
		2																							null							|	eccezione
		3																											null			|	eccezione
		4			null							null			null			null											|	ok
		5			notOk							notOk			notOk			notOk											|	ok
		************************************************************************************ 
		*/
		
		final String ID = "id";
		final String productId = "product_id";
		final String partnerId = "partner_id";
		final String productUomId = "product_uom_id";
		final String sequence = "sequence";
		final String productName = "product_name";
		final String productCode = "product_code";
		
		
		List<Object[]> tests = new ArrayList<>();
		
		//0 
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				new HashMap<>() {{ put(ID,Optional.of(1)); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.of(1));	put(productName, Optional.of("prod001"));	put(productCode, Optional.of("prod001"));	}},
							} );
		//1
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, null);								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//2
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, null);								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//3
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, null);							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//4
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, null);				put(productName, null);				put(productCode, null);				}},
				new HashMap<>() {{ put(ID,Optional.empty()); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.empty());	put(productName, Optional.empty());	put(productCode, Optional.empty());	}},
							} );		
		//5
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, "1");				put(productName, 1);				put(productCode, 1);				}},
				new HashMap<>() {{ put(ID,Optional.empty()); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.empty());	put(productName, Optional.empty());	put(productCode, Optional.empty());	}},
							} );
		
		return tests;
	}
	
	public ProdottoFornitoreDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void test() {
		final String ID = "id";
		final String productId = "product_id";
		final String partnerId = "partner_id";
		final String productUomId = "product_uom_id";
		final String sequence = "sequence";
		final String productName = "product_name";
		final String productCode = "product_code";
		
		
		ProdottoFornitoreDTO prodF = null;
		try {
			prodF = new ProdottoFornitoreDTO(in);
			assertThat(prodF)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("sequence", out.get(sequence))
				.hasFieldOrPropertyWithValue("productName", out.get(productName))
				.hasFieldOrPropertyWithValue("productCode", out.get(productCode))
			    .extracting(
			        ProdottoFornitoreDTO::getId,
			        ProdottoFornitoreDTO::getSequence,
			        ProdottoFornitoreDTO::getProductName,
			        ProdottoFornitoreDTO::getProductCode
			    )
			    .containsExactly(
			    		out.get(ID),
			    		out.get(sequence),
			    		out.get(productName),
			    		out.get(productName)
			    		);
			
			assertThat(prodF.getProductId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(productId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(productId))[1] );
			    });
			
			assertThat(prodF.getPartnerId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(partnerId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(partnerId))[1] );
			    });
			
			assertThat(prodF.getProductUomId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(productUomId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(productUomId))[1] );
			    });
			

		}catch(Exception e) {
			/* Almeno uno tra i campi productID, partnerId e productUomId : 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( Arrays.asList( new Object[] { in.get(productId),in.get(partnerId), in.get(productUomId) }  ) )
		    				.anyMatch(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
}
