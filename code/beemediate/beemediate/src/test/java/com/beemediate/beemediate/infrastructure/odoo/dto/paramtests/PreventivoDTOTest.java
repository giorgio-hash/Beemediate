package com.beemediate.beemediate.infrastructure.odoo.dto;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.assertj.core.util.Arrays;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.springframework.boot.test.context.SpringBootTest;

@SpringBootTest
@RunWith(Parameterized.class)
public class PreventivoDTOTest {

	private Map<String, Object> in;
	private Map<String, Object> out;
	
	
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String name = "name";
		final String partnerId = "partner_id";
		final String productId = "product_id";
		final String currencyId = "currency_id";
		final String pickingTypeId = "picking_type_id";
		final String companyId = "company_id";
		final String origin = "origin";
		final String orderLine = "order_line";
		final String dateOrder = "date_order";
		final String dateApprove = "date_approve";
		final String datePlanned = "date_planned";
		
		final DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
		
		List<Object[]> tests = new ArrayList<>();
		
		/*	CASE		id			name		partnerId		productId		currencytId		pickingTypeId		companyId			origin			orderLine		dateOrder		dateApprove			datePlanned		|ESITO
		 * 	0																																																				|ok
		 * 	1									null																																										|eccezione
		 *	2													notOk																																						|eccezione
		 *	3																	null																																		|eccezione
		 *	4																					notOk																														|eccezione
		 *	5																										null																									|eccezione
		 	6			notOk		notOk																								notOk			notOK			notOK			notOk				notOK			|ok
		 	7			null		null																								null			null			null			null				null			|ok
		 * */
		
		//0
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, "refID001"});							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 													put(dateApprove, "1947-09-09 01:01:01"); 												put(datePlanned, "1947-09-09 01:01:01"); }},
				new HashMap<>() {{ put(ID, Optional.of(1)); put(name, Optional.of("PR-001")); 	put(partnerId, new Object[] {Optional.of(1), Optional.of("refID001")} ); put(productId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(currencyId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(pickingTypeId, new Object[] {Optional.of(1), Optional.of("refID001")} );put(companyId, new Object[] {Optional.of(1), Optional.of("refID001")} );put(origin, Optional.of("PR-001"));	put(orderLine, Optional.of(new Object[]{"a","b","c"}));  put(dateOrder, Optional.of(LocalDateTime.parse("1947-09-09 01:01:01", formatter)) );	put(dateApprove, Optional.of(LocalDateTime.parse("1947-09-09 01:01:01", formatter)) ); put(datePlanned, Optional.of(LocalDateTime.parse("1947-09-09 01:01:01", formatter)) ); }},
							} );
		//1
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, null );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, "refID001"});							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 									put(dateApprove, "1947-09-09 01:01:01"); 									put(datePlanned, "1947-09-09 01:01:01"); }},
				null
							} );
		//2
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, "refID001"});							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 									put(dateApprove, "1947-09-09 01:01:01"); 									put(datePlanned, "1947-09-09 01:01:01"); }},
				null
							} );
		//3
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, null );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, "refID001"});							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 									put(dateApprove, "1947-09-09 01:01:01"); 									put(datePlanned, "1947-09-09 01:01:01"); }},
				null
							} );
		//4
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, null);							put(companyId, new Object[] {1, "refID001"});							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 									put(dateApprove, "1947-09-09 01:01:01"); 									put(datePlanned, "1947-09-09 01:01:01"); }},
				null
							} );
		//5
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, 1); 				put(name, "PR-001"); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, null);							put(origin, "PR-001"); 				put(orderLine, new Object[]{"a","b","c"});				put(dateOrder, "1947-09-09 01:01:01"); 									put(dateApprove, "1947-09-09 01:01:01"); 									put(datePlanned, "1947-09-09 01:01:01"); }},
				null
							} );
		//6
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, "1"); 				put(name, 1); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, 1});							put(origin, 1); 				put(orderLine, "error");				put(dateOrder, "1947-09-09AAAAAAAA:01:01"); 	put(dateApprove, "1947-09-09AAAAAA:01:01"); 	put(datePlanned, "1947-09paodj:01"); }},
				new HashMap<>() {{ put(ID, Optional.empty()); put(name, Optional.empty()); 	put(partnerId, new Object[] {Optional.of(1), Optional.of("refID001")} ); put(productId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(currencyId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(pickingTypeId, new Object[] {Optional.of(1), Optional.of("refID001")} );put(companyId, new Object[] {Optional.of(1), Optional.empty()} );put(origin, Optional.empty());	put(orderLine, Optional.empty());  		put(dateOrder, Optional.empty());				put(dateApprove, Optional.empty() ); 			put(datePlanned, Optional.empty() ); }},
							} );
		//7
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID, null); 				put(name, null); 				put(partnerId, new Object[] {1, "refID001"} );							 put(productId, new Object[] {1, "refID001"} );								put(currencyId, new Object[] {1, "refID001"} );								put(pickingTypeId, new Object[] {1, "refID001"});							put(companyId, new Object[] {1, 1});							put(origin, null); 				put(orderLine, null);				put(dateOrder, null); 							put(dateApprove, null	); 						put(datePlanned, null	); }},
				new HashMap<>() {{ put(ID, Optional.empty()); put(name, Optional.empty()); 	put(partnerId, new Object[] {Optional.of(1), Optional.of("refID001")} ); put(productId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(currencyId, new Object[] {Optional.of(1), Optional.of("refID001")} );	put(pickingTypeId, new Object[] {Optional.of(1), Optional.of("refID001")} );put(companyId, new Object[] {Optional.of(1), Optional.empty()} );put(origin, Optional.empty());	put(orderLine, Optional.empty());  		put(dateOrder, Optional.empty());				put(dateApprove, Optional.empty() ); 			put(datePlanned, Optional.empty() ); }},
							} );
		
		
		return tests;
	}
	
	
	public PreventivoDTOTest(Map<String,Object> in, Map<String,Object> out) {
		this.in = in;
		this.out = out;
	}
	
	
	@Test
	public void test() {
		
		final String ID = "id";
		final String name = "name";
		final String partnerId = "partner_id";
		final String productId = "product_id";
		final String currencyId = "currency_id";
		final String pickingTypeId = "picking_type_id";
		final String companyId = "company_id";
		final String origin = "origin";
		final String orderLine = "order_line";
		final String dateOrder = "date_order";
		final String dateApprove = "date_approve";
		final String datePlanned = "date_planned";
		
		final DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
		
		PreventivoDTO prev = null;
		
		try {
			
			prev = new PreventivoDTO(in);
			
			assertThat(prev)
					.isNotNull()
					.hasNoNullFieldsOrProperties()
					.hasFieldOrPropertyWithValue("id", out.get(ID))
					.hasFieldOrPropertyWithValue("name", out.get(name))
					.hasFieldOrPropertyWithValue("origin", out.get(origin))
					.hasFieldOrPropertyWithValue("dateOrder", out.get(dateOrder))
					.hasFieldOrPropertyWithValue("dateApprove", out.get(dateApprove))
					.hasFieldOrPropertyWithValue("datePlanned", out.get(datePlanned));
			
			assertThat(prev.getCompanyId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
				        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(companyId))[0] );
				        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(companyId))[1] );
				    });
			
			assertThat(prev.getCurrencyId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
				        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(currencyId))[0] );
				        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(currencyId))[1] );
				    });
			
			assertThat(prev.getPartnerId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
				        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(partnerId))[0] );
				        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(partnerId))[1] );
				    });
			
			assertThat(prev.getProductId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
				        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(productId))[0] );
				        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(productId))[1] );
				    });
			
			assertThat(prev.getPickingTypeId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
				        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(pickingTypeId))[0] );
				        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(pickingTypeId))[1] );
				    });
			
			assertThat(prev.getId())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(ID));
					});
			
			assertThat(prev.getName())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(name));
					});
			
			assertThat(prev.getOrigin())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(origin));
					});
			
			if(prev.getOrderLine().isPresent()) {
				Optional<Object[]> actual = (Optional<Object[]>) prev.getOrderLine();
				Optional<Object[]> expected = (Optional<Object[]>) out.get(orderLine);
				assertThat(actual.get()).contains(expected.get());
			}else {
				assertThat(prev.getOrderLine()).isEmpty();
			}
			
			assertThat(prev.getDateOrder())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(dateOrder));
					});
			
			assertThat(prev.getDateApprove())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(dateApprove));
					});
			
			assertThat(prev.getDatePlanned())
					.isNotNull()
					.isInstanceOfSatisfying(Optional.class, o -> {
						assertEquals(o, out.get(datePlanned));
					});
			
		}catch(Exception e) {
			/* Almeno uno tra i campi di tipo IdentifierDTO ha input a costruttore che
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( Arrays.asList( new Object[] { in.get(partnerId),
														in.get(productId),
														in.get(currencyId),
														in.get(pickingTypeId),
														in.get(companyId)}  ) )
		    				.anyMatch(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
}
