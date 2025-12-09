package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;

import org.junit.Test;

/**
 * Completa i test su <i>String.isSubstr1LessOrEqualThanSubstr2</i> con Statement Coverage. Altri test sono presenti su StringHandlerRandoop.
 */
public class StringHandlerisSubstr1LessOrEqualThanSubstr2Test {

	//completa branch coverage.
	//altri test sono in StringHandlerRandoop.
	
	@Test
	public void test_atLeastOne_StringInputIsNull() {
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2(null, "matteo", 0, 2));
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2("matteo", null, 0, 2));
	}
	
	@Test
	public void test_atLeastOne_StringInputIsEmpty() {
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2("", "matteo", 0, 2));
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2("matteo", "", 0, 2));
	}
	
	@Test
	public void test_oneSubstring_overflowsBounds() {
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2("car", "matteo", 0, 4));
		assertFalse(StringHandler.isSubstr1LessOrEqualThanSubstr2("matteo", "car", 0, 4));
	}
}
