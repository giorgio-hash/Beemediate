package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;



import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.assertj.core.util.Arrays;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.beemediate.beemediate.infrastructure.odoo.dto.ArticoloPreventivoDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

/**
 * Test parametrico per la classe {@link ArticoloPreventivoDTO}.
 * <p>
 * Verifica la robustezza del costruttore che accetta una {@code Map<String, Object>} (tipico output di XML-RPC).
 * Il test copre vari scenari, inclusi:
 * <ul>
 * <li><b>Happy Path:</b> Dati completi e corretti.</li>
 * <li><b>Type Mismatch:</b> Gestione di tipi numerici diversi (es. Integer vs Double).</li>
 * <li><b>Missing Data:</b> Campi opzionali nulli o mancanti.</li>
 * <li><b>Malformed Data:</b> Strutture dati errate (es. array di lunghezza insufficiente per le chiavi esterne).</li>
 * </ul>
 * <p>Schema degli input
<table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASO</th>
            <th>id</th>
            <th>orderId</th>
            <th>productId</th>
            <th>product_qty</th>
            <th>ESITO</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>0</td>
            <td>null/notOk</td>
            <td>orderIdnotOk</td>
            <td>-</td>
            <td>null/notOk</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>1</td>
            <td>-</td>
            <td>-</td>
            <td>productIdnotOk</td>
            <td>null/notOk</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>2</td>
            <td>null/notOk</td>
            <td>-</td>
            <td>productWrong1f</td>
            <td>null/notOk</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>3</td>
            <td>-</td>
            <td>-</td>
            <td>productWrong2f</td>
            <td>null/notOk</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>4</td>
            <td>null/notOk</td>
            <td>orderIdnotOk</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>5</td>
            <td>-</td>
            <td>-</td>
            <td>productIdnotOk</td>
            <td>-</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>6</td>
            <td>null/notOk</td>
            <td>orderWrong1f</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>7</td>
            <td>-</td>
            <td>orderWrong2f</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>8</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td>-</td>
            <td style="text-align: left;">ok</td>
        </tr>
    </tbody>
</table></p>
 */
@RunWith(Parameterized.class)
public class ArticoloPreventivoDTOTest {
	
	
/** Mappa di input che simula la risposta grezza di Odoo via XML-RPC. */
    private Map<String, Object> in;
/** * Mappa dei valori attesi dopo la costruzione del DTO. 
     * Se {@code null}, ci si aspetta che il costruttore fallisca lanciando un'eccezione.
     */
    private Map<String, Object> out;
	
/**
     * Genera la suite di casi di test.
     * <p>
     * Ogni entry nell'array contiene:
     * <ol>
     * <li>La mappa di input (Input Data).</li>
     * <li>La mappa di output attesa (Expected Data) o {@code null} se è attesa un'eccezione.</li>
     * </ol>
     *
     * @return Una collezione di casi di test.
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		/*
	CASO	 		id				orderId			productId			product_qty			|ESITO
		0		null/notOk		null/notOk			null/notOk				null/notOk		|eccezione
		1						null/notOk			null/notOk				null/notOk		|eccezione
		2		null/notOk							null/notOk				null/notOk		|eccezione
		3											null/notOk				null/notOk		|eccezione
		4		null/notOk		null/notOk									null/notOk		|eccezione
		5						null/notOk									null/notOk		|eccezione
		6		null/notOk													null/notOk		|ok		
		7																	null/notOk		|ok
		8		null/notOk		null/notOk			null/notOk								|eccezione
		9						null/notOk			null/notOk								|eccezione
		10		null/notOk							null/notOk								|eccezione
		11											null/notOk								|eccezione
		12		null/notOk		null/notOk													|eccezione
		13						null/notOk													|eccezione
		14		null/notOk																	ok
		15																					ok
		************************************************************************************
		*
		*
		* Posso ridurre il numero di test. Focalizzandomi sugli IdentifierDTO:
		* - caso errato: array troppo piccolo oppure null;
		* - caso ok: array grande o giusto;
		* Tra orderId e productId, basta che solo uno dei due sia errato.
		* 
		* Posso mantenere esaustività pensando productId e orderId un'unica variabile.
		* Posso valutare inoltre i casi dove viene ritornato Optional.empty().
		* 
	CASO	 		id			orderId/productId		product_qty				|ESITO
		0		null/notOk		orderIdnotOk			null/notOk				|eccezione
		1						productIdnotOk			null/notOk				|eccezione
		2		null/notOk		productWrong1f			null/notOk				|ok
		3						productWrong2f  		null/notOk				|ok
		4		null/notOk		orderIdnotOk									|eccezione
		5						productIdnotOk									|eccezione
		6		null/notOk		orderWrong1f									|ok		
		7						orderWrong2f									|ok
		8																		|ok
		************************************************************************************ 
		*/
		
		final String ID = "id";
		final String orderID = "order_id";
		final String productID = "product_id";
		final String productQty = "product_qty";
		
		
		List<Object[]> tests = new ArrayList<>();
		
		//0 orderId null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); put(orderID, null); put(productID, new Object[] { 1, "ID-001" } ); put(productQty,null); }},
				null
							} );
		
		//1 productId null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(orderID, new Object[] { 1, "ID-001" } ); put(productID, null ); put(productQty,null); }},
				null
							} );
		//2 productQty null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 			put(orderID, new Object[] { "uno", "ID-001" } ); 							put(productID, new Object[] { 1, "ID-001" }); 						put(productQty,null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(orderID, new Object[] { Optional.empty(), Optional.of("ID-001") } ); put(productID, new Object[] { Optional.of(1), Optional.of("ID-001") }); put(productQty,Optional.empty()); }},
							} );
		//3 errore in productQty
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(orderID, new Object[] { 1, 1 } ); 							put(productID, new Object[] { 1, "ID-001" }); 								put(productQty,"zaza"); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(orderID, new Object[] { Optional.of(1), Optional.empty() } ); put(productID, new Object[] { Optional.of(1), Optional.of("ID-001") } ); put(productQty,Optional.empty()); }},
							} );
		//4 elemento mancante in orderId
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(orderID, new Object[] { 1 } ); put(productID, new Object[] { 1, "ID-001" }); put(productQty,null); }},
				null
							} );
		//5 elemento mancante in productId
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(orderID, new Object[] { 1, "ID-001" } ); put(productID, new Object[] { 1 }); put(productQty,null); }},
				null
							} );
		//6 productQty intero e ID double
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1.1); 			put(orderID, new Object[] { 1, "ID-001" } ); 							put(productID, new Object[] { "1", "ID-001" }); 							put(productQty,2); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(orderID, new Object[] { Optional.of(1), Optional.of("ID-001") } ); put(productID, new Object[] { Optional.empty(), Optional.of("ID-001") } ); put(productQty,Optional.of(2.0)); }},
							} );
		//7 productQty double
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(orderID, new Object[] { 1, "ID-001" } ); 							put(productID, new Object[] { 1, 1 }); 								put(productQty, 2.1 ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(orderID, new Object[] { Optional.of(1), Optional.of("ID-001") } ); put(productID, new Object[] { Optional.of(1), Optional.empty() } ); put(productQty,Optional.of(2.1)); }},
							} );
		//8 
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1);				 put(orderID, new Object[] { 1, "ID-001" } ); 							put(productID, new Object[] { 1, "ID-001" }); 							put(productQty, 2.1 ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(orderID, new Object[] { Optional.of(1), Optional.of("ID-001") } ); put(productID, new Object[] { Optional.of(1), Optional.of("ID-001") } ); put(productQty,Optional.of(2.1)); }},
							} );
		
		
		return tests;
	}
	
/**
     * Costruttore per il test parametrico.
     * @param in Mappa dati input.
     * @param out Mappa dati attesi (o null).
     */
    public ArticoloPreventivoDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di istanziazione e verifica.
     * <p>
     * Il metodo segue due flussi logici:
     * <ol>
     * <li><b>Flusso di Successo (out != null):</b> Tenta di creare il DTO e asserisce che tutti i campi
     * corrispondano ai valori attesi (inclusi i tipi {@link Optional} e i sotto-oggetti {@link IdentifierDTO}).</li>
     * <li><b>Flusso di Errore Atteso (out == null):</b> Cattura l'eccezione generata dal costruttore e
     * verifica che l'input fornito fosse effettivamente non valido (es. array Odoo malformati), 
     * giustificando così il fallimento.</li>
     * </ol>
     */
    @Test
    public void test() {
		final String ID = "id";
		final String orderID = "order_id";
		final String productID = "product_id";
		final String productQty = "product_qty";
		ArticoloPreventivoDTO artPr = null;
		try {
			artPr = new ArticoloPreventivoDTO(in);
			assertThat(artPr)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("productQty", out.get(productQty));
			
			assertThat(artPr.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(artPr.getProductQty())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, qty -> {
				assertEquals(qty, out.get(productQty));
			});
			
			assertThat(artPr.getOrderId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, id -> {
				        assertThat(id.getNum()).isEqualTo( ( (Object[])  out.get(orderID))[0] );
				        assertThat(id.getName()).isEqualTo( ( (Object[])  out.get(orderID))[1] );
				    });
			
			assertThat(artPr.getProductId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, id -> {
			        assertThat(id.getNum()).isEqualTo( ( (Object[])  out.get(productID))[0] );
			        assertThat(id.getName()).isEqualTo( ( (Object[])  out.get(productID))[1] );
			    });
		}catch(Exception e) {
			/* Almeno uno tra i campi productID e orderID dati in input rispetta una delle seguenti condizioni : 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( Arrays.asList( new Object[] { in.get(productID),in.get(orderID) }  ) )
		    				.anyMatch(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
}
