package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class StringHandlerContainsChar {

	//completamento branch+statement coverage.
	//estende i test di StringHandlerRandoop.
	
	@Test
	public void test_null() {
		assertFalse(StringHandler.containsChar(null, '4'));
	}
	
	@Test
	public void test_actuallyContains_c() {
		assertTrue(StringHandler.containsChar("4bigail", '4'));
	}
}
