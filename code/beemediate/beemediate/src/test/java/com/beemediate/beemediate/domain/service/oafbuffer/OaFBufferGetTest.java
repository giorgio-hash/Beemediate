package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

/**
 * Test class for OaFBuffer get operations.
 * This class tests the retrieval of the BoundedBuffer from the OaFBuffer instance.
 */
public class OaFBufferGetTest {

	/**
	 * Mock instance of OrderProviderPort.
	 * Used to simulate order provider behavior in tests.
	 */
	@Mock
	private OrderProviderPort or;
	
	/**
	 * Mock instance of BoundedBuffer.
	 * Used to simulate buffer behavior in tests.
	 */
	@Mock
	private  BoundedBuffer buffer;
	
	/**
	 * Mock instance of OaFValidatorIF.
	 * Used to simulate validator behavior in tests.
	 */
	@Mock
	private OaFValidatorIF validator;
	
	/**
	 * Instance of OaFBuffer to be tested.
	 * Automatically injected with mock dependencies.
	 */
	@InjectMocks
	private OaFBuffer ob;
	
	/**
	 * Setup method executed before each test.
	 * Initializes all mock objects using Mockito.
	 */
	@Before
	public void setup() {
		
		MockitoAnnotations.openMocks(this);

	}
	
	
	/**
	 * Test method to verify that getBuffer() returns the same buffer instance.
	 * Verifies that the buffer retrieved from OaFBuffer is the same object
	 * that was injected (same memory reference).
	 */
	@Test
	public void test() {
		
		BoundedBuffer expected = buffer;
		BoundedBuffer actual = ob.getBuffer();
		assertEquals("Struttura in output uguale a quella in input (stesso pointer)",actual,expected);
	}
}