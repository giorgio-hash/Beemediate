package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class StringHandlerIsDigitTest {

	
	@Test
	public void testInput_whenNonZero() {
		
		assertFalse(StringHandler.isDigit('/', true));
		assertFalse(StringHandler.isDigit('0', true));
		assertTrue(StringHandler.isDigit('1', true));
		assertTrue(StringHandler.isDigit('2', true));
		assertTrue(StringHandler.isDigit('3', true));
		assertTrue(StringHandler.isDigit('4', true));
		assertTrue(StringHandler.isDigit('5', true));
		assertTrue(StringHandler.isDigit('6', true));
		assertTrue(StringHandler.isDigit('7', true));
		assertTrue(StringHandler.isDigit('8', true));
		assertTrue(StringHandler.isDigit('9', true));
		assertFalse(StringHandler.isDigit('{', true));
	}
	
	@Test
	public void testInput_whenCanBeZero() {
		
		assertFalse(StringHandler.isDigit('/', false));
		assertTrue(StringHandler.isDigit('0', false));
		assertTrue(StringHandler.isDigit('1', false));
		assertTrue(StringHandler.isDigit('2', false));
		assertTrue(StringHandler.isDigit('3', false));
		assertTrue(StringHandler.isDigit('4', false));
		assertTrue(StringHandler.isDigit('5', false));
		assertTrue(StringHandler.isDigit('6', false));
		assertTrue(StringHandler.isDigit('7', false));
		assertTrue(StringHandler.isDigit('8', false));
		assertTrue(StringHandler.isDigit('9', false));
		assertFalse(StringHandler.isDigit('{', false));
	}
}
