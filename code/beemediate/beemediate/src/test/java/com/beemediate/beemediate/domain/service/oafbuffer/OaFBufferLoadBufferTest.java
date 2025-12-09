package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
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
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

/**
 * Classe di test parametrizzato per verificare il comportamento del metodo loadNewBuffer()
 * della classe OaFBuffer in scenari ripetuti con diverse configurazioni di input.
 *
 * Questo test usa Mockito per creare doppi di test (mock) di OrderProviderPort, BoundedBuffer
 * e OaFValidatorIF e sostituisce i comportamenti tramite risposte personalizzate che
 * manipolano due Stack<Order> in memoria: uno che rappresenta gli ordini in arrivo (newOrdersStackMock)
 * e uno che rappresenta il contenuto del buffer limitato (bbStackMock).
 *
 * Importante: la classe è progettata per coprire i branch critici del codice mediante un approccio
 * MCDC (Modified Condition/Decision Coverage). La matrice dei casi di test e i commenti MCDC
 * sono presenti all'interno della classe (commento da riga 106 a 121) e non sono stati modificati:
 * tali commenti descrivono esplicitamente le decisioni logiche verificate (ad es. or.fetchOrders(),
 * buffer.isFull(), or.hasNewOrder()) e i casi necessari per ottenere una copertura MCDC.
 *
 * Ogni caso parametrizzato fornisce:
 * - uno Stack di input che simula gli ordini in arrivo,
 * - uno Stack che simula lo stato iniziale del BoundedBuffer,
 * - uno Stack atteso di ordini residui (se il buffer si è riempito),
 * - lo stato atteso del buffer dopo l'esecuzione,
 * - il valore di ritorno atteso del metodo loadNewBuffer().
 *
 * Note:
 * - Le asserzioni nel test confrontano gli identificativi degli ordini (orderID) per evitare
 *   confronti di riferimento diretti sugli oggetti Order.
 * - Il setup dei mock definisce comportamenti side-effect (pop, push, empty, isFull, getSize)
 *   in funzione dei due stack in memoria, consentendo di replicare fedelmente gli scenari
 *   descritti nel commento MCDC.
 *
 * @see com.beemediate.beemediate.domain.service.oafbuffer.OaFBuffer#loadNewBuffer()
 */
@RunWith(Parameterized.class)
public class OaFBufferLoadBufferTest {
	
	/**
 * Mock di OrderProviderPort usato per simulare la sorgente di ordini in arrivo.
 * Viene configurato nel metodo setup() per rispondere a fetchOrders(), hasNewOrder()
 * e popNewOrder() in funzione del contenuto di newOrdersStackMock.
 */
	@Mock
	private OrderProviderPort or;
/**
 * Stack locale che simula la coda degli ordini in arrivo forniti da OrderProviderPort.
 * Viene manipulato dai Answer configurati sui mock per restituire e rimuovere ordini con pop().
 */
	private Stack<Order> newOrdersStackMock;
	
/**
 * Mock di BoundedBuffer usato per simulare il buffer limitato. Le sue operazioni push(),
 * isFull(), empty() e getSize() sono emulate per aggiornare e leggere lo stato del
 * bbStackMock, permettendo test deterministici del metodo loadNewBuffer().
 */
	@Mock
	private  BoundedBuffer buffer;
/**
 * Stack che rappresenta lo stato interno del BoundedBuffer durante i test.
 * Le operazioni sul mock del buffer aggiornano questo stack per riflettere
 * l'inserimento e la rimozione degli ordini.
 */
	private Stack<Order> bbStackMock;
	
/**
 * Mock dell'interfaccia OaFValidatorIF. Presente per iniettare la dipendenza nella
 * classe sotto test; le interazioni con questo mock possono essere estese se necessario.
 */
	@Mock
	private OaFValidatorIF validator;

/**
 * Istanza della classe sotto test (parzialmente mockata tramite @InjectMocks).
 * Rappresenta l'unità funzionale che implementa loadNewBuffer() e che verrà
 * sollecitata nei metodi di test.
 */
	@InjectMocks
	private OaFBuffer ob;
	
/**
 * Stack atteso degli ordini in arrivo dopo l'esecuzione del test.
 * Viene confrontato con newOrdersStackMock per verificare che gli ordini rimasti
 * siano quelli previsti (ad es. se il buffer si è riempito).
 */
	private Stack<Order> expectedNewOrdersStackMock;
/**
 * Stack atteso che rappresenta il contenuto del buffer dopo l'esecuzione del test.
 * Viene confrontato con bbStackMock (mediante confronto sugli orderID) per verificare
 * che gli elementi siano stati aggiornati correttamente.
 */
	private Stack<Order> expectedBbStackMock;

/**
 * Risultato atteso del metodo loadNewBuffer() per il caso parametrizzato corrente.
 * Viene usato nell'asserzione principale per verificare il valore di ritorno della funzione.
 */
	private int expectedResult;
	
	
/**
 * Metodo di setup eseguito prima di ogni test.
 *
 * - Inizializza i mock tramite MockitoAnnotations.openMocks(this).
 * - Configura il comportamento del mock OrderProviderPort:
 *   - fetchOrders() e hasNewOrder() ritornano true se newOrdersStackMock non è vuoto.
 *   - popNewOrder() rimuove e restituisce l'elemento superiore di newOrdersStackMock.
 * - Configura il comportamento del mock BoundedBuffer:
 *   - push(Order) aggiunge l'ordine a bbStackMock (side-effect simulato).
 *   - isFull() è valutato in base alla dimensione di bbStackMock (qui: pieno se size==1).
 *   - empty() svuota bbStackMock.
 *   - getSize() ritorna la dimensione attuale di bbStackMock.
 *
 * Scopo: predisporre l'ambiente per eseguire scenari deterministici che verificano
 * i branch e le condizioni logiche necessari al raggiungimento della copertura MCDC.
 */
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
/**
 * Metodo factory dei parametri per i test parametrizzati (@Parameters).
 *
 * Restituisce una Collection di Object[] dove ogni elemento rappresenta un caso di test
 * completo: array di input { newOrdersStack, bbStack } e array di output attesi
 * { expectedNewOrdersStack, expectedBbStack, expectedResult }.
 *
 * I casi inclusi sono costruiti per esercitare:
 * - la decisione iniziale basata su or.fetchOrders()
 * - il comportamento quando il buffer è pieno o non pieno
 * - la condizione di loop controllata da or.hasNewOrder()
 *
 * Questi casi concorrono alla copertura MCDC dichiarata nella documentazione di classe.
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
						new Stack<>() {{ push(new Order(null, "o1")); }},
						new Stack<>() {{ push(new Order(null, "o2")); }},
						1
				},
			});
		return tests;
	}
	
/**
 * Costruttore del test parametrizzato.
 *
 * Riceve gli oggetti input e output per il singolo caso di test (forniti dal metodo parameters())
 * e mappa i valori nei campi di istanza:
 * - newOrdersStackMock, bbStackMock: stati iniziali che simulano provider e buffer.
 * - expectedNewOrdersStackMock, expectedBbStackMock, expectedResult: valori attesi per le asserzioni.
 *
 * @param inputs array contenente gli stack di input {newOrdersStack, bbStack}
 * @param outputs array contenente gli stack/valore attesi {expectedNewOrdersStack, expectedBbStack, expectedResult}
 */
	@SuppressWarnings("unchecked")
	public OaFBufferLoadBufferTest(Object[] inputs, Object[] outputs) {
		
		newOrdersStackMock = (Stack<Order>) inputs[0];
		bbStackMock = (Stack<Order>) inputs[1];
		
		expectedNewOrdersStackMock = (Stack<Order>) outputs[0];
		expectedBbStackMock = (Stack<Order>) outputs[1];
		expectedResult = (int) outputs[2];
	}
	
	
/**
 * Metodo di test principale.
 *
 * - Invoca ob.loadNewBuffer() e verifica che il valore restituito corrisponda a expectedResult.
 * - Confronta il contenuto attuale del buffer (bbStackMock) con expectedBbStackMock controllando
 *   gli orderID per assicurare che gli elementi precedenti siano eliminati e che i nuovi
 *   elementi siano stati inseriti correttamente quando previsto.
 * - Verifica che gli ordini in arrivo residui (newOrdersStackMock) corrispondano alla
 *   condizione attesa (ad es. rimangono ordini solo se il buffer è pieno).
 *
 * Le asserzioni sono costruite per validare sia lo stato finale degli stack sia la
 * correttezza del valore di ritorno, consentendo di misurare il comportamento
 * funzionale richiesto e la copertura delle condizioni MCDC.
 */
	@Test
	public void test() {
	
		int result = ob.loadNewBuffer();
		assertEquals("output funzione",expectedResult,result);
		
		String[] expectedBbIds = bbStackMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		String[] bBIds = expectedBbStackMock.stream().map(o -> o.getOrderID()).toArray(String[]::new);
		assertTrue("Gli elementi precedenti vengono eliminati e, se esistono, nuovi elementi in arrivo vengono aggiunti", Arrays.deepEquals(expectedBbIds, bBIds));

		assertEquals("Rimangono ordini in arrivo solo se il buffer è pieno",expectedNewOrdersStackMock.isEmpty(),newOrdersStackMock.isEmpty());
		
	}
}
