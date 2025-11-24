package com.beemediate.beemediate.domain.pojo;

import org.junit.Test;

import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;

import static org.junit.Assert.*;

/**
 * Test del Copy Constructor e del toString.
 */
public class ConfirmationStructureTest {


    @Test
    public void testCopyConstructor_CorrectlyCopiesAllFields() {
 
        ConfirmationStructure original = createFullConfirmation();

 
        ConfirmationStructure copy = new ConfirmationStructure(original);

 
        

        assertNotSame("La copia deve essere una nuova istanza", original, copy);
        

        assertEquals(original.getOrderResponseDate(), copy.getOrderResponseDate());
        assertEquals(original.getDeliveryDate(), copy.getDeliveryDate());
        assertEquals(original.getOrderId(), copy.getOrderId());
        assertEquals(original.getOrderIdGealan(), copy.getOrderIdGealan());
        assertEquals(original.getAddressName(), copy.getAddressName());
        assertEquals(original.getAddressStreet(), copy.getAddressStreet());
        assertEquals(original.getAddressZip(), copy.getAddressZip());
        assertEquals(original.getAddressCity(), copy.getAddressCity());
        assertEquals(original.getAddressCountry(), copy.getAddressCountry());
        assertEquals(original.getAddressCountryCoded(), copy.getAddressCountryCoded());
        assertEquals(original.getCurrency(), copy.getCurrency());
        

        assertEquals(original.getTotalItemNum(), copy.getTotalItemNum());

        assertEquals(original.getTotalAmount(), copy.getTotalAmount(), 0.0f);
    }


    @Test
    public void testCopyConstructor_ThrowsExceptionOnNull() {
        assertThrows(NullPointerException.class, () -> {
        	new ConfirmationStructure(null);
        });
    }


    @Test
    public void testToString_ReturnsCorrectFormat() {
    	
        ConfirmationStructure confirmation = new ConfirmationStructure();
        confirmation.setOrderResponseDate("2023-10-25");
        confirmation.setDeliveryDate("2023-11-01");
        confirmation.setOrderId("ORD-123");
        confirmation.setOrderIdGealan("GEA-456");
        confirmation.setAddressName("Mario Rossi");
        confirmation.setAddressStreet("Via Roma 1");
        confirmation.setAddressZip("00100");
        confirmation.setAddressCity("Roma");
        confirmation.setAddressCountry("Italy");
        confirmation.setAddressCountryCoded("IT");
        confirmation.setTotalItemNum(5);
        confirmation.setTotalAmount(150.50f);
        confirmation.setCurrency("EUR");

        String result = confirmation.toString();
        
        String expected = "ConfirmationStructure [" +
                "orderResponseDate=2023-10-25" + 
                "deliveryDate=2023-11-01, " +
                "orderId=ORD-123, " +
                "orderIdGealan=GEA-456, " +
                "addressName=Mario Rossi, " +
                "addressStreet=Via Roma 1, " +
                "addressZip=00100, " +
                "addressCity=Roma, " +
                "addressCountry=Italy, " +
                "addressCountryCoded=IT, " +
                "totalItemNum=5, " +
                "totalAmount=150.5, " + 
                "currency=EUR]";

        assertEquals(expected, result);
    }

    // --- Helper Method per popolare i dati ---
    private ConfirmationStructure createFullConfirmation() {
        ConfirmationStructure cs = new ConfirmationStructure();
        cs.setOrderResponseDate("2023-01-01");
        cs.setDeliveryDate("2023-01-10");
        cs.setOrderId("100");
        cs.setOrderIdGealan("G-100");
        cs.setAddressName("Azienda Test");
        cs.setAddressStreet("Via Test 1");
        cs.setAddressZip("12345");
        cs.setAddressCity("Milano");
        cs.setAddressCountry("Italia");
        cs.setAddressCountryCoded("IT");
        cs.setTotalItemNum(10);
        cs.setTotalAmount(99.99f);
        cs.setCurrency("EUR");
        return cs;
    }
}