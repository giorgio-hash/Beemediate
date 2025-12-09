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


	/**
 * Capacità del buffer utilizzata per la parametrizzazione del test.
 *
 * <p>
 * Può assumere valori negativi (caso non valido), zero (buffer senza capienza),
 * o valori positivi (dimensioni effettive del buffer). Il valore è fornito
 * dal metodo parametrizzato {@code parameters()} e passato al costruttore del test.
 * </p>
 */
    private int capacity;
/**
 * Istanza del BoundedBuffer sotto test.
 *
 * <p>
 * Viene inizializzata nel metodo {@code setUp()} prima di ogni test. Per capacità
 * non valide (es. negative) il campo rimane {@code null} e il test verifica che la
 * creazione del buffer sollevi un'eccezione.
 * </p>
 */
    private BoundedBuffer buffer;
	

/**
 * Fornisce i parametri usati dal runner Parameterized.
 *
 * <p>
 * Restituisce una collezione di array di oggetti, ciascuno contenente un singolo
 * parametro intero che rappresenta la capacità del buffer da testare.
 * I parametri inclusi sono: -1, 0 e 5.
 * </p>
 *
 * @return una Collection di Object[] contenente i valori di capacità per i test
 */
	@Parameters
	public static Collection<Object[]> parameters() {
        return Arrays.asList(new Object[][]{
                {-1}, {0}, {5}
        });
    }

/**
 * Costruttore del test parametrizzato.
 *
 * <p>
 * Il parametro {@code capacity} viene memorizzato per essere utilizzato nella
 * fase di setup e nelle asserzioni dei singoli test. Viene passato automaticamente
 * dal runner Parameterized per ogni istanza del test.
 * </p>
 *
 * @param capacity la capacità del buffer per questa istanza di test
 */
    public BoundedBufferParameterizedTest(int capacity) {
        this.capacity = capacity;
    }

/**
 * Inizializza lo stato prima di ogni test.
 *
 * <p>
 * Se {@code capacity > 0} crea una nuova istanza di {@code BoundedBuffer} con la
 * capacità specificata. Se {@code capacity} non è positiva, il test si aspetta
 * che la costruzione del buffer sollevi un'eccezione e lascia il campo {@code buffer}
 * a {@code null}.
 * </p>
 *
 * <p>
 * Questo metodo prepara le condizioni iniziali per i metodi di test successivi.
 * </p>
 */
    @Before
    public void setUp() {
    	if(capacity>0)
    		buffer = new BoundedBuffer(capacity);
    	else {
    		buffer = null;
    		assertThrows(Exception.class, () -> {
    			buffer = new BoundedBuffer(capacity);
    		});
    	}
    }

/**
 * Verifica lo stato iniziale del buffer per capacità positive.
 *
 * <p>
 * Controlla che:
 * <ul>
 *   <li>la capacità del buffer corrisponda al valore fornito;</li>
 *   <li>la dimensione iniziale sia 0;</li>
 *   <li>il buffer sia vuoto ({@code isEmpty() == true});</li>
 *   <li>il buffer non sia pieno ({@code isFull() == false}).</li>
 * </ul>
 * I controlli sono eseguiti solo quando {@code capacity > 0}.
 * </p>
 */
    @Test
    public void testInitialState() {
    	
    	if(capacity>0) {
            assertEquals("capacity()", capacity, buffer.capacity());
            assertEquals("getSize() initial", 0, buffer.getSize());
            assertTrue("isEmpty() initial", buffer.isEmpty());
            assertFalse("isFull() initial", buffer.isFull());
    	}
    }

/**
 * Testa il riempimento fino alla capacità e il comportamento in caso di overflow.
 *
 * <p>
 * Azioni verificate (per {@code capacity > 0}):
 * <ul>
 *   <li>inserire esattamente {@code capacity} elementi con {@code push};</li>
 *   <li>verificare che la dimensione sia uguale a {@code capacity} e {@code isFull() == true};</li>
 *   <li>verificare che un ulteriore {@code push} non incrementi la dimensione (no-op quando è pieno);</li>
 *   <li>controllare che l'elemento nella posizione {@code capacity-1} sia l'ultimo inserito che ha trovato posto;</li>
 *   <li>controllare che {@code get(-1)} e {@code get(capacity)} restituiscano {@code null} per indici fuori intervallo.</li>
 * </ul>
 * </p>
 */
    @Test
    public void testFillToCapacityAndOverflow() {
    	
        // push exactly capacity elements
    	if(capacity>0) {
    		
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
	        
	        Order underflow = buffer.get(-1);
	        assertNull("buffer.get(-1) returns null", underflow);
	        Order overflow = buffer.get(capacity);
	        assertNull("buffer.get(buffer.capacity()) returns null", overflow);
    	}
    }

/**
 * Verifica il comportamento LIFO di {@code pop()} su un sottoinsieme di elementi.
 *
 * <p>
 * Se {@code capacity >= 3} inserisce fino a 3 elementi (o fino alla capacità se minore)
 * e li rimuove verificando l'ordine LIFO (ultimo inserito, primo rimosso).
 * Dopo le rimozioni la dimensione deve essere 0 e {@code isEmpty() == true}.
 *
 * <p>
 * Se {@code 0 < capacity < 3} esegue un controllo ridotto: inserisce un elemento,
 * esegue {@code pop()} e verifica che la dimensione torni a 0 e che il buffer sia vuoto.
 * </p>
 */
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
    		if(capacity>0) {
        		buffer.push(new Order(new OrderStructure(), "p" + 0));
        		assertEquals("size after pushes", 1, buffer.getSize());
        		Order popped = buffer.pop();
        		assertNotNull("popped not null", popped);
        		assertEquals("size after pops", 0, buffer.getSize());
        		assertTrue("isEmpty after pops", buffer.isEmpty());
    		}
    	}
    }
    
/**
 * Testa il metodo {@code empty()} che svuota il buffer.
 *
 * <p>
 * Per {@code capacity > 0} il test:
 * <ol>
 *   <li>inserisce due elementi;</li>
 *   <li>invoca {@code empty()};</li>
 *   <li>verifica che la dimensione sia 0 e che {@code isEmpty() == true};</li>
 *   <li>verifica lo stato di {@code isFull()} in base alla capacità (per chiarezza logica,
 *       il buffer non deve risultare pieno dopo uno svuotamento se {@code capacity > 0}).</li>
 * </ol>
 * </p>
 */
    @Test
    public void testEmptyFunction() {
    	if(capacity>0) {
	    	buffer.push(new Order(new OrderStructure(), "p" + 0));
	    	buffer.push(new Order(new OrderStructure(), "p" + 1));
	    	buffer.empty();
	    	assertTrue("buffer is full only if capacity==0", buffer.capacity()>0?	!buffer.isFull() : buffer.isFull());
	    	assertTrue("buffer is empty", buffer.isEmpty());
	    	assertEquals("size after", 0, buffer.getSize());
    	}
    }
}