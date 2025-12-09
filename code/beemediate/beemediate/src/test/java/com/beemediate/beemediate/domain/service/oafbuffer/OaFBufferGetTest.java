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

public class OaFBufferGetTest {

	@Mock
	private OrderProviderPort or;
	
	@Mock
	private  BoundedBuffer buffer;
	
	@Mock
	private OaFValidatorIF validator;
	
	@InjectMocks
	private OaFBuffer ob;
	
	@Before
	public void setup() {
		
		MockitoAnnotations.openMocks(this);

	}
	
	
	@Test
	public void test() {
		
		BoundedBuffer expected = buffer;
		BoundedBuffer actual = ob.getBuffer();
		assertEquals("Struttura in output uguale a quella in input (stesso pointer)",actual,expected);
	}
}