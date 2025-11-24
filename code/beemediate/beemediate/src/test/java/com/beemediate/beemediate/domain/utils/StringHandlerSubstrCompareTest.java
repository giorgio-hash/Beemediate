package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

public class StringHandlerSubstrCompareTest {

	//completa branch coverage e statement coverage.
	//estende i test in StringHandlerRandoop.
	
	@Test
	public void test_substr1GreaterThanSubstr2() {
		
		assertEquals(1, StringHandler.substrCompare("21", "111", 0, 1));
		
	}
}
