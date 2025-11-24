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

@RunWith(Parameterized.class)
public class OaFBufferValidateBufferTest {

	@Mock
	private OrderProviderPort or;
	
	@Mock
	private  BoundedBuffer buffer;
	private List<Order> bbMock;
	
	@Mock
	private OaFValidatorIF validator;
	
	@InjectMocks
	private OaFBuffer ob;
	
	private int expectedResult;
	
	@Before
	public void setup() {
		
		MockitoAnnotations.openMocks(this);
		
		
		//buffer = mock(BoundedBuffer.class);
		doAnswer(invocation -> {
		    Order t = invocation.getArgument(0);
		    bbMock.add(t);
		    return null; 
		}).when(buffer).push(any(Order.class));
		when(buffer.getSize()).then(new Answer<Integer>() {
			@Override
			public Integer answer(InvocationOnMock invocation) throws Throwable {
				return bbMock.size();
			}
		});
		when(buffer.get(anyInt())).then(invocation -> {
			int t = invocation.getArgument(0);
		    return bbMock.get(t);
		});
		
		//validator = mock(OaFValidatorIF.class);
		doAnswer(invocation -> {
			return null;
		}).when(validator).validate(any(Order.class));
	}
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		List<Object[]> tests = new ArrayList<>();
		tests.add(new Object[] {
				new ArrayList<>(), //buffer vuoto
				0
			});
		tests.add(new Object[] {
			new ArrayList<>() {{ 
						add(new Order(null, "o1") {{	//ordine corretto	
							setCustomerNumber(true);
							setDeliveryLocationNumber(true);
							setDeliveryDate(true);
							setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
							setArticleNumber(true);
							setQuantityMeasure(true);
							setDeliveryDateContent(true);
						}}); 
					}},
			1
		});
		tests.add(new Object[] {
				new ArrayList<>() {{ 
							add(new Order(null, "o1") {{	//ordine ContentError	
								setCustomerNumber(true);
								setDeliveryLocationNumber(true);
								setDeliveryDate(true);
								setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
								setArticleNumber(false);
								setQuantityMeasure(true);
								setDeliveryDateContent(true);
							}}); 
						}},
				1
			});
		tests.add(new Object[] {
				new ArrayList<>() {{ 
							add(new Order(null, "o1") {{	//ordine OpenTransError	
								setCustomerNumber(true);
								setDeliveryLocationNumber(true);
								setDeliveryDate(true);
								setQuantity(QuantityFieldValue.NAN);
								setArticleNumber(true);
								setQuantityMeasure(true);
								setDeliveryDateContent(true);
							}}); 
						}},
				0
			});
		tests.add(new Object[] {
				new ArrayList<>() {{ 
							add(new Order(null, "o1") {{	//ordine OpenTransError	
								setCustomerNumber(true);
								setDeliveryLocationNumber(true);
								setDeliveryDate(true);
								setQuantity(QuantityFieldValue.NAN);
								setArticleNumber(true);
								setQuantityMeasure(true);
								setDeliveryDateContent(true);
							}}); 
							add(new Order(null, "o2") {{	//ordine ContentError	
								setCustomerNumber(true);
								setDeliveryLocationNumber(true);
								setDeliveryDate(true);
								setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
								setArticleNumber(false);
								setQuantityMeasure(true);
								setDeliveryDateContent(true);
							}});
							add(new Order(null, "o3") {{	//ordine corretto	
								setCustomerNumber(true);
								setDeliveryLocationNumber(true);
								setDeliveryDate(true);
								setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
								setArticleNumber(true);
								setQuantityMeasure(true);
								setDeliveryDateContent(true);
							}}); 
						}},
				2
			});
		return tests;
	}
	
	public OaFBufferValidateBufferTest(List<Order> input, int output) {
		bbMock = input;
		expectedResult = output;
	}
	
	@Test
	public void test() {
		
		String[] expectedBbIds = bbMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		int result = ob.validateBuffer();
		String[] bBIds = bbMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		
		assertEquals("numero di ordini validi per essere inviati", result, expectedResult);
		assertTrue("buffer immutato", Arrays.deepEquals(expectedBbIds, bBIds));
	}
	
}
