package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * Estende i test di StringHanderRandoop
 */
public class StringHandlerContainsChar {

	//completamento branch+statement coverage.
	//estende i test di StringHandlerRandoop.
	
	/**
	 * testa il caso con input str==null
	 */
	@Test
	public void test_null() {
		assertFalse(StringHandler.containsChar(null, '4'));
	}
	
	/**
	 * testa il caso in cui output "true"
	 */
	@Test
	public void test_actuallyContains_c() {
		assertTrue(StringHandler.containsChar("4bigail", '4'));
	}
}
