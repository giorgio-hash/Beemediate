package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.when;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Stack;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;

import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.QuantityFieldValue;
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