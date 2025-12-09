package com.beemediate.beemediate.domain.service.OaFValidator;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.when;

import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.domain.exceptions.EmptyArrayException;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.pojo.order.OrderSummary;
import com.beemediate.beemediate.domain.pojo.order.QuantityFieldValue;
import com.beemediate.beemediate.domain.ports.infrastructure.filesystem.SupplierCatalogReaderPort;
import com.beemediate.beemediate.domain.service.validator.impl.OaFValidator;

/**Testing usando lo scenario sendOrder.avalla
 */
public class OaFValidatorValidateTest {

	@Mock
	private SupplierCatalogReaderPort catalog;
	
	private OaFValidator ov;
	
	public OaFValidatorValidateTest() throws EmptyArrayException {
		MockitoAnnotations.openMocks(this);
		when(catalog.readArticleNumbers()).thenReturn(new String[] {"aaa","bbb","ccc"});
		
		ov = new OaFValidator(catalog);
	}
	
	
	@Test
	public void test_fromAvalla_state0(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.INTEGER, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state1(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	
	@Test
	public void test_fromAvalla_state2(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("302400509150");	//<---------------------ERRORE
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//variante 2
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID(null);	//<---------------------ERRORE
		oh.setBuyerIDRef("3024005150");
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 3
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef(null);	//<---------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 4
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID(null);	
		oh.setBuyerIDRef(null);	//<---------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 5
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("30245150");	//<---------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 6
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("302400");	//<---------------------ERRORE
		oh.setBuyerIDRef("302400");	//<---------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertFalse(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state3(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("30248j5150");		//<----------------------------ERRORE
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertFalse(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//variante 2
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("30901505150");		
		oh.setDeliveryIDRef("30901505150");
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 3
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("30901505150");		//<----------------------------ERRORE
		oh.setDeliveryIDRef("3024005150");		//<----------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertFalse(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 4
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID(null);		//<----------------------------ERRORE
		oh.setDeliveryIDRef("3024005150");		
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertFalse(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 5
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("30901505150");		
		oh.setDeliveryIDRef(null);		//<----------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertFalse(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//variante 6
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("30901505150");		
		oh.setDeliveryIDRef("sdosih");		//<----------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertFalse(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state4(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-01:11:11");//<--------------------------ERRORE
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
		//Variante 2
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		oh.setStartDate(null);//<--------------------------ERRORE
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
		//Variante 3
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09:11");//<--------------------------ERRORE
		oh.setOrderDate("2025-09-12T11:11:11");
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
		//Variante 4
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate(null);//<--------------------------ERRORE
		oh.setOrderDate("2025-09-12T11:11:11");
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
		//Variante 5
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("20212T11:11:11");//<--------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
		//Variante 6
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate(null);//<--------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertFalse(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state5(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1,0");//<-----------------------------ERRORE
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_COMMA, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state6(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.khd");//<--------------------------------------ERRORE
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.NAN, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//Variante 2
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity(null);//<--------------------------------------ERRORE
		ov.validate(o);
		assertTrue("ha opentranserror",o.hasOpenTransError());
		assertFalse("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.NAN, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
	
	@Test
	public void test_fromAvalla_state7(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("3242");//<------------------------------------------ERRORE
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertFalse(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//variante 2
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID(null);//<------------------------------------------ERRORE
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertFalse(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}	
	
	@Test
	public void test_fromAvalla_state8(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("Ml");//<----------------------------------------ERRORE
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertFalse(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//variante 2
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit(null);//<----------------------------------------ERRORE
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertFalse(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//variante 3
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("a");//<----------------------------------------ERRORE
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertFalse(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertTrue(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}

	@Test
	public void test_fromAvalla_state9(){
		OrderStructure ost = new OrderStructure();
		OrderHeader oh = new OrderHeader();
		OrderItem oi = new OrderItem();
		OrderSummary os = new OrderSummary();
		
		//customerNumber
		/**
		 * Deve essere "3024005150"
		 */
		oh.setBuyerID("3024005150");	
		oh.setBuyerIDRef("3024005150");
		
		//deliveryLocationNumber
		/**
		 * Deve essere "3024005150"/"30901505150"
		 */
		oh.setDeliveryID("3024005150");
		oh.setDeliveryIDRef("3024005150");
		
		//articleNumber
		/**
		 * Deve essere "aaa"/"bbb"/"ccc"
		 */
		oi.setSupplierID("aaa");
		
		//quantityMeasure
		/**
		 * Deve essere M
		 */
		oi.setOrderUnit("M");
		
		//quantity
		/**
		 * Deve essere INTEGER oppure FLOAT_WITH_DOT
		 */
		oi.setQuantity("1.0");
		
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-13T11:11:11");			//<------------------ERRORE
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-12T11:11:11");
		
		ost.setHeader(oh);
		ost.setOrderSummary(os);
		ost.setItemList(new OrderItem[] {oi});
		
		Order o = new Order(ost,"o1");
		
		ov.validate(o);
		
		
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		
		//Variante 2
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");			
		oh.setEndDate("2025-09-13T11:11:11");//<------------------ERRORE
		oh.setOrderDate("2025-09-12T11:11:11");
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
		//Variante 3
		//deliveryDateContent
		/**
		 * nessuno deve essere null. Devono essere nella forma DateTime
		 */
		//deliveryDate
		/** start ed end devono essere uguali
		 * start/end deve essere avanti rispetto a order
		 */
		oh.setStartDate("2025-09-12T11:11:11");			
		oh.setEndDate("2025-09-12T11:11:11");
		oh.setOrderDate("2025-09-13T11:11:11"); //<------------------ERRORE
		ov.validate(o);
		assertFalse("ha opentranserror",o.hasOpenTransError());
		assertTrue("ha contenterror",o.hasContentError());
		assertTrue(o.isCustomerNumber());
		assertTrue(o.isArticleNumber());
		assertTrue(o.isQuantityMeasure());
		assertEquals(QuantityFieldValue.FLOAT_WITH_DOT, o.getQuantity());
		assertTrue(o.isDeliveryLocationNumber());
		assertFalse(o.isDeliveryDate());
		assertTrue(o.isDeliveryDateContent());
	}
}
