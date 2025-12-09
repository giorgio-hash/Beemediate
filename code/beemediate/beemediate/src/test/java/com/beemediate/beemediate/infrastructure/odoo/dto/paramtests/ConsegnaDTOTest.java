package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

/**
 * Test parametrico per la classe {@link ConsegnaDTO}.
 * <p>
 * Verifica la logica di deserializzazione dei dati grezzi provenienti da Odoo (Mappa).
 * Il test copre scenari di robustezza e validazione strutturale, in particolare per il campo complesso
 * {@code warehouse_id} che Odoo restituisce come tupla (array di 2 elementi: ID e Nome).
 */
@RunWith(Parameterized.class)
public class ConsegnaDTOTest {

/** Mappa di input simulata (risposta XML-RPC). */
    private Map<String, Object> in;
/** Mappa dei valori attesi dopo il parsing. Se {@code null}, è attesa un'eccezione. */
    private Map<String, Object> out;
	
/**
     * Genera i casi di test.
     * <p>
     * Scenari coperti:
     * <ol>
     * <li><b>Happy Path:</b> ID e WarehouseID corretti e completi.</li>
     * <li><b>Type Mismatch (Safe Parsing):</b> ID o elementi dell'array WarehouseID di tipo errato (es. String invece di Int).
     * In questi casi il DTO deve restituire {@code Optional.empty()} senza rompersi.</li>
     * <li><b>Malformed Data (Exception):</b> Campo {@code warehouse_id} nullo o array di lunghezza errata.
     * In questi casi il costruttore deve fallire.</li>
     * </ol>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String warehouseID = "warehouse_id";
		List<Object[]> tests = new ArrayList<>();
		
		//0 ID ok, warehouseID ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(warehouseID, new Object[] { 1 , "WH/001" } ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(warehouseID, new Object[] { Optional.of(1) , Optional.of("WH/001") } ); }},
							} );
		
		//1 ID notOk, warehouseID ok (id errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(warehouseID, new Object[] { "1" , "WH/001" } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(warehouseID, new Object[] { Optional.empty() , Optional.of("WH/001") } ); }},
							} );

		//2 ID null, warehouseID ok (name errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(warehouseID, new Object[] { 1 , 1 } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(warehouseID, new Object[] { Optional.of(1) , Optional.empty() } ); }},
							} );
		
		//3 ID ok, warehouseID notOk (null)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(warehouseID, null ); }},
				null
							} );

		
		//4 ID notOk, warehouseID notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(warehouseID, new Object[] { 1 } ); }},
				null
							} );

		
		
		return tests;
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Input map.
     * @param out Expected map (o null per eccezione).
     */
    public ConsegnaDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Logica:
     * <ul>
     * <li>Se {@code out != null}: Verifica che il DTO venga creato e che i campi (incluso il sotto-oggetto {@link IdentifierDTO})
     * siano popolati come atteso (inclusi gli {@code Optional.empty()} dovuti a mismatch di tipo).</li>
     * <li>Se {@code out == null}: Si aspetta un'eccezione dal costruttore e verifica che l'input
     * fosse effettivamente malformato (es. {@code warehouse_id} non array o lunghezza errata),
     * confermando che il fallimento è corretto e controllato.</li>
     * </ul>
     */
    @Test
	public void Test() {
		final String ID = "id";
		final String warehouseID = "warehouse_id";
		ConsegnaDTO cons = null;
		try {
			cons = new ConsegnaDTO(in);
			assertThat(cons)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID));
			
			assertThat(cons.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(cons.getWarehouseId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, id -> {
				        assertThat(id.getNum()).isEqualTo( ( (Object[])  out.get(warehouseID))[0] );
				        assertThat(id.getName()).isEqualTo( ( (Object[])  out.get(warehouseID))[1] );
				    });
		}catch(Exception e) {
			/* warehouseID 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( in.get(warehouseID) )
					.matches(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
	
}
