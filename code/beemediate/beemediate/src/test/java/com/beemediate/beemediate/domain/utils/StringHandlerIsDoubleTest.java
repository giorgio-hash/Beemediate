package com.beemediate.beemediate.domain.utils;

import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.Test;

public class StringHandlerIsDoubleTest {
	
	@Test
	public void TestWHen_isDouble_isActuallyDouble() {
		assertTrue(StringHandler.isDouble("9.9"));
	}

}
