package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.assertj.core.util.Arrays;
import org.junit.Test;
import org.junit.jupiter.api.Assertions;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.springframework.boot.test.context.SpringBootTest;

import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

@SpringBootTest
@RunWith(Parameterized.class)
public class IdentifierDTOTest {
	
	private Object[] in;
	private Object[] out;
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		List<Object[]> tests = new ArrayList<Object[]>();
		
		/*
		 * CASE			num			name		in!=null	in.length==2	|ESITO
		 * 	1			null					true		true			|ok
		 * 	2						notOk		true		true			|ok
		 * 	3			notOk		null		true		true			|ok
		 * 	4						-			true		false			|eccezione
		 * 	5			-			-			false		.				|eccezione
		 * ***********************************************************************
		 * */
		
		//1
		tests.add(new Object[] {
				new Object[] { null,			"nome" },
				new Object[] { Optional.empty(),Optional.of("nome") },
		} );
		//2
		tests.add(new Object[] {
				new Object[] { 1,				1 },
				new Object[] { Optional.of(1),Optional.empty() },
		} );
		//3
		tests.add(new Object[] {
				new Object[] { "1",				null },
				new Object[] { Optional.empty(),Optional.empty() },
		} );
		//4
		tests.add(new Object[] {
				new Object[] { 1 },
				null
		} );
		//5
		tests.add(new Object[] {
				null,
				null
		} );
		
		
		return tests;
	}
	
	public IdentifierDTOTest(Object[] in, Object[] out) {
		this.in = in;
		this.out = out;
	}
	
	@Test
	public void Test() {
	
		final int num=0;
		final int name=1;
		
		IdentifierDTO ident = null;
		
		try {
			ident = new IdentifierDTO(in);
			
			assertThat(ident)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("num", out[num])
				.hasFieldOrPropertyWithValue("name", out[name]);

			assertThat(ident.getNum())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out[num]);
				});
			
			assertThat(ident.getName())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out[name]);
				});
				
		}catch(Exception e) {
			/* L'input 
			 * - è null
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat(in).satisfiesAnyOf(
				    o -> assertThat(o).isNull(),
				    o -> assertThat(o).isNotInstanceOf(Object[].class),
				    o -> assertThat(o).isInstanceOfSatisfying(Object[].class, a -> assertThat(a.length).isNotEqualTo(2))
				);
		}
	}

}
