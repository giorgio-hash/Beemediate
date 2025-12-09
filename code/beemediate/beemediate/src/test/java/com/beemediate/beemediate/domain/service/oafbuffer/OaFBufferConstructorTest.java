package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertNotNull;

import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.mock;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;

/**
 * Test class for OaFBuffer constructor using Partition Testing with parameterized test cases.
 * 
 * This class implements partition testing methodology by dividing the input domain
 * (capacity values) into distinct equivalence classes:
 * <ul>
 *   <li>Negative values partition: capacity = -1 (invalid)</li>
 *   <li>Boundary value partition: capacity = 0 (boundary condition)</li>
 *   <li>Valid values partition: capacity = 5 (valid positive value)</li>
 * </ul>
 * 
 * The parameterized test approach allows testing multiple scenarios with different
 * input values while keeping the test logic centralized. Each parameter set is
 * executed as a separate test case.
 * 
 * @see org.junit.runners.Parameterized
 */
@RunWith(Parameterized.class)
public class OaFBufferConstructorTest {

	/**
	 * Capacity parameter used for testing the OaFBuffer constructor.
	 * This value is parameterized and varies across different test executions
	 * based on the partition testing strategy.
	 */
	private int capacity;
	
	/**
	 * Mock instance of OrderProviderPort dependency.
	 * Used for injecting a mock object into OaFBuffer during testing.
	 */
	private OrderProviderPort orderProvMock;
	
	/**
	 * Mock instance of OaFValidatorIF dependency.
	 * Used for injecting a mock validator into OaFBuffer during testing.
	 */
	private OaFValidatorIF vMock;
	
	/**
	 * Provides test parameters for partition testing.
	 * 
	 * Returns three equivalence partitions:
	 * <ul>
	 *   <li>Negative partition: -1 (expects exception)</li>
	 *   <li>Boundary partition: 0 (expects exception)</li>
	 *   <li>Valid partition: 5 (expects successful creation)</li>
	 * </ul>
	 * 
	 * @return Collection of Object arrays containing test parameter values
	 */
	@Parameters
	public static Collection<Object[]> parameters() {
		return Arrays.asList(new Object[][]{
				{-1}, {0}, {5}
		});
	}
	
	/**
	 * Constructor for parameterized test initialization.
	 * 
	 * This constructor is called by the Parameterized test runner for each
	 * parameter set, allowing the capacity parameter to be injected and tested.
	 * 
	 * @param capacity the capacity value from the current partition being tested
	 */
	public OaFBufferConstructorTest(int capacity) {
		this.capacity = capacity;
	}
	
	/**
	 * Setup method executed before each parameterized test execution.
	 * 
	 * Initializes mock objects for OrderProviderPort and OaFValidatorIF
	 * to be used during constructor testing.
	 */
	@Before
	public void setup() {
		orderProvMock = mock(OrderProviderPort.class);
		vMock = mock(OaFValidatorIF.class);
	}
	
	/**
	 * Parameterized test method for OaFBuffer constructor validation.
	 * 
	 * Tests the constructor behavior across different input partitions:
	 * <ul>
	 *   <li>Valid partition (capacity > 0): asserts successful object creation</li>
	 *   <li>Invalid partitions (capacity ≤ 0): asserts that an Exception is thrown</li>
	 * </ul>
	 * 
	 * This test demonstrates partition testing by verifying that each
	 * equivalence class behaves according to specification.
	 */
	@Test
	public void test() {
		
		if(capacity>0)
			assertNotNull("Oggetto creato corretttamente", new OaFBuffer(capacity, vMock , orderProvMock));
		else {
			assertThrows("Oggetto non creato, solleva eccezioni", Exception.class, ()->{
				@SuppressWarnings("unused")
				OaFBuffer oaf = new OaFBuffer(capacity, vMock , orderProvMock);
			});
		}
	}
}
