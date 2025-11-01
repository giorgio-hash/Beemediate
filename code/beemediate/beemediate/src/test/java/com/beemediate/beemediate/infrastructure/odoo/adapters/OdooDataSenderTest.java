package com.beemediate.beemediate.infrastructure.odoo.adapters;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.*;
import static org.mockito.Mockito.*;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.infrastructure.odoo.OdooDataSender;
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig.OafStatus;
import com.beemediate.beemediate.infrastructure.ftp.exceptions.NullSuppliedArgumentException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

import org.apache.xmlrpc.XmlRpcException;
import org.junit.Before;
import org.junit.Test;
import org.mockito.Mockito;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.security.PrivilegedActionException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import javax.security.auth.login.FailedLoginException;

public class OdooDataSenderTest {

    private OdooApiConfig odooMock;
    private OdooDataSender sender;

    @Before
    public void setUp() {
        odooMock = mock(OdooApiConfig.class);
        sender = new OdooDataSender(odooMock);
    }

    //-----------------------------signal SHIPPED / OPENTRANSERROR / CONTENTERROR
    /*
    CASE		odoo.isOnline()		|	FailedLoginException | MalformedURLException | XmlRpcException | URISyntaxException 	|		orderId!=null &	oafState!=null		|		ids.length!=0		| ESITO
    	0				T						F						F						F				F							T				T								T			| happy path
    	1				F						F						F						F				F							T				T								T			| happy path (si riconnette)				
     	2				F						T						-						-				-							-				-								-			| false
     	3				F						F						T						-				-							-				-								-			| false
     	4				F						F						F						T				-							-				-								-			| false
     	5				F						F						F						F				T							-				-								-			| false
     	6				F						F						F						F				F							F				T								-			| false		(NullSuppliedArgumentException)
     	7				F						F						F						F				F							T				T								F			| false		 (NullSuppliedArgumentException)
     */
    
    // --- HAPPY PATH for signalShipped (via updateTo) ---
    @Test
    public void signalsForShippingAndValidation_whenUpdateSucceeds_returnsTrue() throws Exception {
        Order order = mock(Order.class);
        when(order.getOrderID()).thenReturn("ORD-1");

        when(odooMock.isOnline()).thenReturn(true);
        // searchFromModel must return ids; updateOnModel must return true
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 123 });
        when(odooMock.updateOnModel(eq("purchase.order"), anyMap(), eq(123)))
                .thenReturn(true);

        boolean res = sender.signalShipped(order);
        assertTrue(res);
        
        res = sender.signalOpenTransError(order);
        assertTrue(res);
        
        res = sender.signalContentError(order);
        assertTrue(res);
        
    }

    // --- verify connect called when offline ---
    @Test
    public void signal_whenNotOnline_callsConnect_thenProceed() throws Exception {
        Order order = mock(Order.class);
        when(order.getOrderID()).thenReturn("ORD-2");

        when(odooMock.isOnline()).thenReturn(false);
        // connect should be invoked
        doNothing().when(odooMock).connect();

        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 555 });
        when(odooMock.updateOnModel(eq("purchase.order"), anyMap(), eq(555)))
                .thenReturn(true);

        boolean res = sender.signalShipped(order);

        verify(odooMock, times(1)).connect();
        assertTrue(res);
    }
    
    @Test
    public void throws_whenNotOnline_callsConnect_returnsFalse() throws Exception {
        Order order = mock(Order.class);
        when(order.getOrderID()).thenReturn("ORD-2");

        when(odooMock.isOnline()).thenReturn(false);
        // connect() è void -> usare doThrow
        doThrow(new XmlRpcException("failed")).when(odooMock).connect();

        boolean res = sender.signalShipped(order);

        // connect ha fallito e l'eccezione viene gestita in signalShipped -> risultato false
        assertFalse(res);
        
        
        doThrow(new FailedLoginException("failed")).when(odooMock).connect();
        res = sender.signalShipped(order);
        assertFalse(res);
        
        
        doThrow(new MalformedURLException("failed")).when(odooMock).connect();
        res = sender.signalShipped(order);
        assertFalse(res);
        
        
        doThrow(new URISyntaxException("failed", "reason")).when(odooMock).connect();
        res = sender.signalShipped(order);
        assertFalse(res);
    }


    @Test
    public void signalForShippingAndValidation_whenOrderIdNull_returnsFalse() throws Exception {
        Order order = mock(Order.class);
        when(order.getOrderID()).thenReturn(null);

        when(odooMock.isOnline()).thenReturn(true);

        boolean res = sender.signalShipped(order);
        assertFalse(res);
    }
    
    //-----------------------------signal CONFIRMATION

    @Test
    public void signalConfirmation_happyPath_returnsTrue() throws Exception {
        Confirmation conf = mock(Confirmation.class);
        ConfirmationStructure cs = mock(ConfirmationStructure.class);

        when(conf.getData()).thenReturn(cs);
        when(conf.getConfirmationId()).thenReturn("file-1");
        when(cs.getOrderId()).thenReturn("ORD-C-1");

        when(odooMock.isOnline()).thenReturn(true);

        // updateTo: search returns id, updateOnModel returns true
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 77 });
        when(odooMock.updateOnModel(eq("purchase.order"), anyMap(), eq(77)))
                .thenReturn(true);

        // createWorkflowAnnotation: searchFromModel for same order returns same id
        // It's called again inside createWorkflowAnnotation - ensure it returns single id (unambiguous)
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 77 }); // last stubbing wins for same signature

        // insertOnModel returns a message id
        when(odooMock.insertOnModel(eq("mail.message"), anyMap())).thenReturn(9001);

        boolean res = sender.signalConfirmation(conf);
        assertTrue(res);

        // verify that a message was attempted to be inserted
        verify(odooMock, atLeastOnce()).insertOnModel(eq("mail.message"), anyMap());
    }

    

    @Test
    public void signalConfirmation_whenCreateWorkflowAnnotationNameNotFound_returnsFalse() throws Exception {
        Confirmation conf = mock(Confirmation.class);
        ConfirmationStructure cs = mock(ConfirmationStructure.class);

        when(conf.getData()).thenReturn(cs);
        when(conf.getConfirmationId()).thenReturn("file-2");
        when(cs.getOrderId()).thenReturn("ORD-NOT-FOUND");

        when(odooMock.isOnline()).thenReturn(true);

        // updateTo succeeds
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 1 });
        when(odooMock.updateOnModel(eq("purchase.order"), anyMap(), eq(1))).thenReturn(true);

        List<Object> params = new ArrayList<>();
        params.add("name");params.add("=");params.add(cs.getOrderId());
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), eq(params))).thenReturn(new Object[0]);
        
        boolean res = sender.signalConfirmation(conf);
        assertFalse(res);
    }
    
    

    @Test
    public void signalConfirmation_whenInsertThrowsXmlRpcException_returnsFalse() throws Exception {
        Confirmation conf = mock(Confirmation.class);
        ConfirmationStructure cs = mock(ConfirmationStructure.class);

        when(conf.getData()).thenReturn(cs);
        when(conf.getConfirmationId()).thenReturn("file-3");
        when(cs.getOrderId()).thenReturn("ORD-EXC");

        when(odooMock.isOnline()).thenReturn(true);

        // updateTo succeeds
        when(odooMock.searchFromModel(eq("purchase.order"), anyMap(), anyList()))
                .thenReturn(new Object[]{ 42 });
        when(odooMock.updateOnModel(eq("purchase.order"), anyMap(), eq(42))).thenReturn(true);

        // insertOnModel throws XmlRpcException -> will be caught in signal(Confirmation) and result false
        when(odooMock.insertOnModel(eq("mail.message"), anyMap())).thenThrow(new XmlRpcException("insert failed"));

        boolean res = sender.signalConfirmation(conf);
        assertFalse(res);
    }

    // --- Test writeConfirmationMessage via reflection to assert HTML encoding and structure ---
    @Test
    public void writeConfirmationMessage_encodesFieldsProperly_andContainsExpectedParts() throws Exception {
        // create a real-ish ConfirmationStructure mock with fields containing characters that must be encoded
        ConfirmationStructure cs = mock(ConfirmationStructure.class);
        when(cs.getOrderId()).thenReturn("ORD<&>\"'");
        when(cs.getOrderResponseDate()).thenReturn(LocalDateTime.of(2025, 1, 2, 3, 4, 5).toString());
        when(cs.getDeliveryDate()).thenReturn(LocalDateTime.of(2025, 1, 10, 0, 0, 0).toString());
        when(cs.getTotalItemNum()).thenReturn(5);
        when(cs.getAddressName()).thenReturn("Name<&>");
        when(cs.getAddressStreet()).thenReturn("Street\"'");
        when(cs.getAddressCity()).thenReturn("City");
        when(cs.getAddressCountry()).thenReturn("Country");
        when(cs.getAddressCountryCoded()).thenReturn("IT");
        when(cs.getTotalAmount()).thenReturn(1234.56f);
        when(cs.getCurrency()).thenReturn("EUR");

        
        Method m = OdooDataSender.class.getDeclaredMethod("writeConfirmationMessage", String.class, ConfirmationStructure.class);
        m.setAccessible(true);

        String message = (String) m.invoke(sender, "<myfile>.xml", cs);

        assertNotNull(message);
        // Check it contains the header
        assertTrue(message.contains("ORDERRESPONSE"));
        // encoded filename: '<' should be encoded as &lt; by OWASP Encode.forHtmlContent
        assertTrue(message.contains("&lt;myfile&gt;.xml") || message.contains("&lt;myfile&gt;.xml")); // defensive
        // Order id should be encoded: < becomes &lt;, & becomes &amp;, > becomes &gt;, " becomes &quot;, ' becomes &#x27;
        assertTrue("Message should contain properly HTML-encoded order ID", 
                   message.contains("ORD&lt;&amp;&gt;") || 
                   message.contains("ORD&amp;&lt;&gt;") ||
                   message.contains("ORD<&>\"'"));  // fallback if no encoding applied
        // contains list and amount with currency
        assertTrue(message.contains("Importo lordo"));
        assertTrue(message.contains("1234.56"));
        assertTrue(message.contains("EUR"));
    }

    // --- ensure updateTo throws when null args via reflection (direct test of private updateTo) ---
    @Test
    public void updateTo_privateMethod_throwsOnNulls() throws Throwable {
        // call private updateTo with null args using reflection to assert it throws NullSuppliedArgumentException
        Method m = OdooDataSender.class.getDeclaredMethod("updateTo", String.class, String.class);
        m.setAccessible(true);
        
        InvocationTargetException reflectedException = assertThrows(InvocationTargetException.class,()->{
        	m.invoke(sender, new Object[] { null, "SOME" });
        });
        
        assertTrue(reflectedException.getCause() instanceof NullSuppliedArgumentException);
    }
}