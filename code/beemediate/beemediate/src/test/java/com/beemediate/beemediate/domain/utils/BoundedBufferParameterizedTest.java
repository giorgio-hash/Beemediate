package com.beemediate.beemediate.domain.utils;

import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.*;

/**
 * Test parametrico: verifica comportamento per varie capacità del buffer,
 * inclusi test per empty().
 */
@RunWith(Parameterized.class)
public class BoundedBufferParameterizedTest {

    @Parameterized.Parameters(name = "capacity={0}")
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {1}, {2}, {5}, {10}
        });
    }

    private final int capacity;
    private BoundedBuffer buffer;

    public BoundedBufferParameterizedTest(int capacity) {
        this.capacity = capacity;
    }

    @Before
    public void setUp() {
        buffer = new BoundedBuffer(capacity);
    }

    @Test
    public void testInitialState() {
        assertEquals("capacity()", capacity, buffer.capacity());
        assertEquals("getSize() initial", 0, buffer.getSize());
        assertTrue("isEmpty() initial", buffer.isEmpty());
        assertFalse("isFull() initial", buffer.isFull());
    }

    @Test
    public void testFillToCapacityAndOverflow() {
        // push exactly capacity elements
        for (int i = 0; i < capacity; i++) {
            buffer.push(new Order(new OrderStructure(), "o" + i));
        }
        assertEquals("size after fill", capacity, buffer.getSize());
        assertTrue("isFull() after fill", buffer.isFull());
        assertFalse("isEmpty() after fill", buffer.isEmpty());

        // pushing one more element should not increase size (push is no-op when full)
        Order extra = new Order(new OrderStructure(), "extra");
        buffer.push(extra);
        assertEquals("size after overflow attempt", capacity, buffer.getSize());

        // ensure top element is the last one that fit (LIFO): ordini[capacity-1] should be "o{capacity-1}"
        Order top = buffer.get(capacity - 1);
        assertNotNull("top element exists", top);
        assertEquals("top id remains the last pushed within capacity", "o" + (capacity - 1), top.getOrderID());
    }

    @Test
    public void testLifoPopPartial() {
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
    }

    @Test
    public void testEmptyOnVariousStates() {
        // 1) empty() on already empty buffer
        assertEquals(0, buffer.getSize());
        buffer.empty();
        assertEquals("size remains 0 after empty on empty", 0, buffer.getSize());
        assertTrue("isEmpty after empty on empty", buffer.isEmpty());
        assertEquals("capacity unchanged", capacity, buffer.capacity());

        // 2) empty() after partial fill
        int partial = Math.min(3, capacity);
        for (int i = 0; i < partial; i++) {
            buffer.push(new Order(new OrderStructure(), "a" + i));
        }
        assertEquals(partial, buffer.getSize());
        buffer.empty();
        assertEquals("size 0 after empty()", 0, buffer.getSize());
        assertTrue("isEmpty after empty()", buffer.isEmpty());
        // all indices should now return null (get returns null for i>=size)
        for (int i = 0; i < capacity; i++) {
            assertNull("get(" + i + ") should be null after empty()", buffer.get(i));
        }

        // 3) empty() after full fill
        for (int i = 0; i < capacity; i++) {
            buffer.push(new Order(new OrderStructure(), "f" + i));
        }
        assertEquals(capacity, buffer.getSize());
        buffer.empty();
        assertEquals("size 0 after empty() when full", 0, buffer.getSize());
        assertTrue("isEmpty after empty() when full", buffer.isEmpty());
        assertEquals("capacity unchanged after empty", capacity, buffer.capacity());
        for (int i = 0; i < capacity; i++) {
            assertNull("get(" + i + ") should be null after empty() (full->empty)", buffer.get(i));
        }
        // pop after empty should return null
        assertNull("pop after empty should be null", buffer.pop());
    }
}