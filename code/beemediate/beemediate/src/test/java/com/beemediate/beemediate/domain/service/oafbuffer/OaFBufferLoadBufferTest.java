package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.mock;
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
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

@RunWith(Parameterized.class)
public class OaFBufferLoadBufferTest {
	
	@Mock
	private OrderProviderPort or;
	private Stack<Order> newOrdersStackMock;
	
	@Mock
	private  BoundedBuffer buffer;
	private Stack<Order> bbStackMock;
	
	@Mock
	private OaFValidatorIF validator;

	@InjectMocks
	private OaFBuffer ob;
	
	
	private Stack<Order> expectedNewOrdersStackMock;
	private Stack<Order> expectedBbStackMock;
	private int expectedResult;
	
	
	
	@Before
	public void setup() {
		
		MockitoAnnotations.openMocks(this);
		//or = mock(OrderProviderPort.class);
		when(or.fetchOrders()).thenAnswer(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				return !newOrdersStackMock.isEmpty();
			}
		});
		when(or.hasNewOrder()).thenAnswer(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				return !newOrdersStackMock.isEmpty();
			}
		});
		when(or.popNewOrder()).thenAnswer(new Answer<Order>() {
			@Override
			public Order answer(InvocationOnMock invocation) throws Throwable {
				return newOrdersStackMock.pop();
			}
		});
		
		
		//buffer = mock(BoundedBuffer.class);
		doAnswer(invocation -> {
		    Order t = invocation.getArgument(0);
		    bbStackMock.add(t);
		    return null; 
		}).when(buffer).push(any(Order.class));
		when(buffer.isFull()).thenAnswer(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				return bbStackMock.size()==1;
			}
		});
		doAnswer(invocation -> {
			bbStackMock.clear();
			return null;
		}).when(buffer).empty();
		when(buffer.getSize()).then(new Answer<Integer>() {
			@Override
			public Integer answer(InvocationOnMock invocation) throws Throwable {
				return bbStackMock.size();
			}
		});
	}

	//if(or.fetchOrders())
	/**CASE		or.fetchOrders()	|	Esito dec.	|	Esito metodo		|	inputs
	 * 1		T					|	true		|	(va in 'then')		|	newOrdersStackMock[1] { o1 }, buffer[1] { o1Old }
	 * 2		F					|	false		|	(finisce il metodo)	|	newOrdersStackMock[1] { }, buffer[1] { o1Old }
	 */
	
	//if(buffer.isFull())
	/**CASE		buffer.isFull()		|	Esito dec.	|	Esito metodo										|	inputs
	 * 3		T					|	true		|	rompe il ciclo anche prima di consumare stack		|	newOrdersStackMock[2] { o1, o2 }, buffer[1] { o1Old }
	 * 4		F					|	false		|	raggiunge decisione 'while'							|	newOrdersStackMock[1] { o1 }, buffer[1] { o1Old }
	 */
	
	/**CASE		or.hasNewOrder()	|	Esito dec.	|	Esito metodo			|	inputs
	 * 5		T					|	true		|	ricomincia il loop		|	newOrdersStackMock[2] { o1, o2 }, buffer[1] { o1Old }
	 * 6		F					|	false		|	prosegue verso la fine	|	newOrdersStackMock[1] { o1 }, buffer[1] { o1Old }
	 */
	
	@Parameters
	public static Collection<Object[]> parameters() {
		
		List<Object[]> tests = new ArrayList<>();
		tests.add(new Object[] {
			new Object[] {//input
					new Stack<>() {{ push(new Order(null, "o1")); }},
					new Stack<>() {{ push(new Order(null, "o1Old")); }}
			},
			new Object[] {//expected output
					new Stack<>() {{ }},
					new Stack<>() {{ push(new Order(null, "o1")); }},
					1
			},
		});
		tests.add(new Object[] {
				new Object[] {//input
						new Stack<>() {{ }},
						new Stack<>() {{ push(new Order(null, "o1Old")); }}
				},
				new Object[] {//expected output
						new Stack<>() {{ }},
						new Stack<>() {{ }},
						0
				},
			});
		tests.add(new Object[] {
				new Object[] {//input
						new Stack<>() {{ push(new Order(null, "o1"));push(new Order(null, "o2")); }},
						new Stack<>() {{ push(new Order(null, "o1Old")); }}
				},
				new Object[] {//expected output
						new Stack<>() {{ }},
						new Stack<>() {{ push(new Order(null, "o2")); }},
						1
				},
			});
		return tests;
	}
	
	
	@SuppressWarnings("unchecked")
	public OaFBufferLoadBufferTest(Object[] inputs, Object[] outputs) {
		
		newOrdersStackMock = (Stack<Order>) inputs[0];
		bbStackMock = (Stack<Order>) inputs[1];
		
		expectedNewOrdersStackMock = (Stack<Order>) outputs[0];
		expectedBbStackMock = (Stack<Order>) outputs[1];
		expectedResult = (int) outputs[2];
	}
	
	
	
	@Test
	public void test() {
	
		int result = ob.loadNewBuffer();
		assertEquals("output funzione",expectedResult,result);
		
		String[] expectedBbIds = bbStackMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		String[] bBIds = expectedBbStackMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		assertTrue("gli elementi precedenti vengono eliminati e, se esistono, nuovi elementi in arrivo vengono aggiunti", Arrays.deepEquals(expectedBbIds, bBIds));

		assertEquals("il buffer degli ordini in arrivo si svuota",expectedNewOrdersStackMock.isEmpty(),newOrdersStackMock.isEmpty());
		
	}
}
