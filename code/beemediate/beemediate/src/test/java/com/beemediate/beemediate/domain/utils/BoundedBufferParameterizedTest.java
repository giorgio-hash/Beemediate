package com.beemediate.beemediate.domain.utils;

import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.*;

/**
 * Test parametrico: verifica comportamento per varie capacità del buffer,
 * inclusi test per empty().
 */
@RunWith(Parameterized.class)
public class BoundedBufferParameterizedTest {


    private int capacity;
    private BoundedBuffer buffer;
	
	@Parameters
	public static Collection<Object[]> parameters() {
        return Arrays.asList(new Object[][]{
                {-1}, {0}, {5}
        });
    }

    public BoundedBufferParameterizedTest(int capacity) {
        this.capacity = capacity;
    }

    @Before
    public void setUp() {
    	if(capacity>=0)
    		buffer = new BoundedBuffer(capacity);
    	else {
    		buffer = null;
    		assertThrows(Exception.class, () -> {
    			buffer = new BoundedBuffer(capacity);
    		});
    	}
    }

    @Test
    public void testInitialState() {
    	
    	if(capacity>=0) {
            assertEquals("capacity()", capacity, buffer.capacity());
            assertEquals("getSize() initial", 0, buffer.getSize());
            if(capacity==0) {
            	assertTrue("isEmpty() initial", buffer.isEmpty());
            	assertTrue("isFull() initial", buffer.isFull());
            }else {
            	assertTrue("isEmpty() initial", buffer.isEmpty());
            	assertFalse("isFull() initial", buffer.isFull());
            }
    	}
    }

    @Test
    public void testFillToCapacityAndOverflow() {
    	
        // push exactly capacity elements
    	if(capacity>=0) {
    		
	        for (int i = 0; i < capacity; i++) {
	            buffer.push(new Order(new OrderStructure(), "o" + i));
	        }
	        assertEquals("size after fill", capacity, buffer.getSize());
	        assertTrue("isFull() after fill", buffer.isFull());
	        
	        assertTrue("isEmpty() after fill", capacity>0?	!buffer.isEmpty() : buffer.isEmpty() );
	
	        // pushing one more element should not increase size (push is no-op when full)
	        Order extra = new Order(new OrderStructure(), "extra");
	        buffer.push(extra);
	        assertEquals("size after overflow attempt", capacity, buffer.getSize());
	
	        // ensure top element is the last one that fit (LIFO): ordini[capacity-1] should be "o{capacity-1}"
	        Order top = buffer.get(capacity - 1);
	        if(capacity>0) {
		        assertNotNull("top element exists", top);
		        assertEquals("top id remains the last pushed within capacity", "o" + (capacity - 1), top.getOrderID());	
	        }else {
	        	assertNull("empty buffer returns null", top);
	        }
	        
	        Order underflow = buffer.get(-1);
	        assertNull("buffer.get(-1) returns null", underflow);
	        Order overflow = buffer.get(capacity);
	        assertNull("buffer.get(buffer.capacity()) returns null", overflow);
    	}
    }

    @Test
    public void testLifoPopPartial() {
    	if(capacity>=3) {
	        // push up to 3 elements or capacity, whichever smaller
	        int n = Math.min(3, capacity);
	        for (int i = 0; i < n; i++) {
	            buffer.push(new Order(new OrderStructure(), "p" + i));
	        }
	        assertEquals("size after pushes", n, buffer.getSize());
	        // pop them and verify LIFO order
	        for (int i = n - 1; i >= 0; i--) {
	            Order popped = buffer.pop();
	            assertNotNull("popped not null", popped);
	            assertEquals("popped id", "p" + i, popped.getOrderID());
	        }
	        assertEquals("size after pops", 0, buffer.getSize());
	        assertTrue("isEmpty after pops", buffer.isEmpty());
    	}else {
    		if(capacity>=0) {
        		buffer.push(new Order(new OrderStructure(), "p" + 0));
        		if(capacity>0) {
        			assertEquals("size after pushes", 1, buffer.getSize());
        			Order popped = buffer.pop();
        			assertNotNull("popped not null", popped);
        		}else {
        			assertEquals("size after pushes", 0, buffer.getSize());
        			Order popped = buffer.pop();
        			assertNull("popped null", popped);
        		}
        		
        		assertEquals("size after pops", 0, buffer.getSize());
        		assertTrue("isEmpty after pops", buffer.isEmpty());
    		}
    	}
    }
    
    @Test
    public void testEmptyFunction() {
    	if(capacity>=0) {
	    	buffer.push(new Order(new OrderStructure(), "p" + 0));
	    	buffer.push(new Order(new OrderStructure(), "p" + 1));
	    	buffer.empty();
	    	assertTrue("buffer is full only if capacity==0", buffer.capacity()>0?	!buffer.isFull() : buffer.isFull());
	    	assertTrue("buffer is empty", buffer.isEmpty());
	    	assertEquals("size after", 0, buffer.getSize());
    	}
    }
}