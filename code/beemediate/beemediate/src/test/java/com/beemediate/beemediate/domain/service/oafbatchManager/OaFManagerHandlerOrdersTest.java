package com.beemediate.beemediate.domain.service;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import org.junit.Before;
import org.junit.Test;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;

import com.beemediate.beemediate.domain.exceptions.UnreachableThresholdException;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.QuantityFieldValue;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.ConfirmationProviderPort;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

/**
 * 
 * test per verificare gestione ordini.
 * - implementazione scenario noOrder.avalla
 * - implementazione scenario sendOrder.avalla
 */
public class OaFManagerHandlerOrdersTest {

	private OaFBuffer oafMock;
	
	private BoundedBuffer buffer;	
	
	private ConfirmationProviderPort confirmationsMock;

	private FTPHandlerPort ftpMock;

	private DataSenderPort crmMock;
	
	private OaFBatchManager oafb;
	
	private Order o;
	
	private int sendToInbound;
	private int signalShipped;
	private int sendOpenTransError;
	private int sendContentError;
	
	
	@Before
	public void setup() throws UnreachableThresholdException {
		
		sendToInbound=0;
		signalShipped=0;
		sendOpenTransError=0;
		sendContentError=0;
		
		o = new Order(null,null);
		oafMock = mock(OaFBuffer.class);
		confirmationsMock = mock(ConfirmationProviderPort.class);
		ftpMock = mock(FTPHandlerPort.class);
		crmMock = mock(DataSenderPort.class);
		
		
		buffer = new BoundedBuffer(1);
		buffer.push(o);
		when(oafMock.loadNewBuffer()).thenReturn(buffer.getSize());
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		
		when(oafMock.validateBuffer()).thenAnswer(new Answer<Integer>() {
		    @Override
		    public Integer answer(InvocationOnMock invocation) throws Throwable {
		    	
		    	int validOrd=0;
		    	for(int i=0; i<buffer.getSize(); i++) {
		    		if(!buffer.get(i).hasOpenTransError())
		    			validOrd++;
		    	}
		    	
		        return validOrd;
		    }
		});
		when(crmMock.signalOpenTransError(any(Order.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				sendOpenTransError += 1;
				return true;
			}
		});
		when(crmMock.signalContentError(any(Order.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				sendContentError += 1;
				return true;
			}
		});
		when(crmMock.signalShipped(any(Order.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				signalShipped += 1;
				return true;
			}
		});
		when(ftpMock.loadOrder(any(Order.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				sendToInbound += 1;
				return true;
			}
		});
		
		oafb = new OaFBatchManager(1, oafMock, confirmationsMock, ftpMock,  crmMock);
		
	}
	
	//---------------------------------------------Scenario noOrder.avalla
	
	@Test
	public void test_noOrder_state0() {
	
		buffer.empty();
		when(oafMock.loadNewBuffer()).thenReturn(buffer.getSize());
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		int result = oafb.handleOrders();
		
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		assertEquals("Numero di ordini inviati", 0, signalShipped);
	}
	
	
	//---------------------------------------------Scenario sendOrder.avalla
	@Test
	public void test_sendOrder_state0() {
		//monitored input da state0 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.INTEGER);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state1 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state1() {
		//monitored input da state1 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state2 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}

	@Test
	public void test_sendOrder_state2() {
		//monitored input da state2 del modello
		o.setCustomerNumber(false);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertTrue("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state3 del modello
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state3() {
		//monitored input da state3 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(false);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertTrue("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state4 del modello
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state4() {
		//monitored input da state4 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(false);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertTrue("Order ha Content Error",o.hasContentError());
		assertTrue("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state5 del modello
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);//è "meno rilevante"
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state5() {
		//monitored input da state5 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_COMMA);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertTrue("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state6 del modello
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state6() {
		//monitored input da state6 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.NAN);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertTrue("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state7 del modello
		assertEquals("ordine caricato a inbound",0,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",0,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state7() {
		//monitored input da state7 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(false);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertTrue("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state8 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",1, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, sendContentError);
		assertEquals("Nessun ordine è stato segnalato come \"SHIPPED\"", 0, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state8() {
		//monitored input da state8 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(false);
		o.setDeliveryDateContent(true);
		
		assertTrue("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state9 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",1, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, sendContentError);
		assertEquals("Nessun ordine è stato segnalato come \"SHIPPED\"", 0, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	@Test
	public void test_sendOrder_state9() {
		//monitored input da state9 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(false);
		
		assertTrue("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state10 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",1, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, sendContentError);
		assertEquals("Nessun ordine è stato segnalato come \"SHIPPED\"", 0, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	
	@Test
	public void test_sendOrder_state10() {
		//monitored input da state10 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		
		assertFalse("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		
		int result = oafb.handleOrders();
		
		//controlled da state11 del modello
		assertEquals("ordine caricato a inbound",1,sendToInbound);
		assertEquals("content error signal",0, sendContentError);
		assertEquals("OpenTrans error signal",0, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",1,result);
		assertEquals("Numero di ordini inviati", result, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}
	
	
	
	//---------------------------------------------Multi-ordine

	@Test
	public void test_multiOrders_state0_state2_state7() {
		
		//resetto il mock
		buffer = new BoundedBuffer(3);
		Order o2 = new Order(null,null);
		Order o7 = new Order(null,null);
		buffer.push(o);
		buffer.push(o2);
		buffer.push(o7);
		when(oafMock.loadNewBuffer()).thenReturn(buffer.getSize());
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		//monitored input da state0 del modello
		o.setCustomerNumber(true);
		o.setDeliveryLocationNumber(true);
		o.setDeliveryDate(true);
		o.setQuantity(QuantityFieldValue.INTEGER);
		o.setArticleNumber(true);
		o.setQuantityMeasure(true);
		o.setDeliveryDateContent(true);
		assertFalse("Order ha Content Error",o.hasContentError());
		assertFalse("Order ha OpenTrans Error",o.hasOpenTransError());
		//monitored input da state2 del modello
		o2.setCustomerNumber(false);
		o2.setDeliveryLocationNumber(true);
		o2.setDeliveryDate(true);
		o2.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o2.setArticleNumber(true);
		o2.setQuantityMeasure(true);
		o2.setDeliveryDateContent(true);	
		assertFalse("Order ha Content Error",o2.hasContentError());
		assertTrue("Order ha OpenTrans Error",o2.hasOpenTransError());
		//monitored input da state7 del modello
		o7.setCustomerNumber(true);
		o7.setDeliveryLocationNumber(true);
		o7.setDeliveryDate(true);
		o7.setQuantity(QuantityFieldValue.FLOAT_WITH_DOT);
		o7.setArticleNumber(false);
		o7.setQuantityMeasure(true);
		o7.setDeliveryDateContent(true);	
		assertTrue("Order ha Content Error",o7.hasContentError());
		assertFalse("Order ha OpenTrans Error",o7.hasOpenTransError());
		

		
		int result = oafb.handleOrders();
		
		//somma dei controlled da state0, state2, state7 del modello
		assertEquals("ordine caricato a inbound",2,sendToInbound);
		assertEquals("content error signal",1, sendContentError);
		assertEquals("OpenTrans error signal",1, sendOpenTransError);
		
		//specifico dell'implementazione (differenze dal modello)
		assertEquals("Ordini effettivamente processati",2,result);
		assertEquals("Numero di ordini inviati", result, signalShipped+sendContentError);
		assertEquals("Ordini senza errori", 1, signalShipped);
		assertTrue("Il buffer degli ordini in arrivo è svuotato", buffer.isEmpty());
	}

}
