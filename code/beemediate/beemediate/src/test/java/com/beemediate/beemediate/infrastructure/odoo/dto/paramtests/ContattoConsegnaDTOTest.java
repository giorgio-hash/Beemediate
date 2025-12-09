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

import com.beemediate.beemediate.infrastructure.odoo.dto.ContattoConsegnaDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

/**
 * Test parametrico per la classe {@link ContattoConsegnaDTO}.
 * <p>
 * Verifica la logica di deserializzazione dei dati grezzi provenienti da Odoo (Mappa).
 * Il test si concentra sulla gestione del campo complesso {@code partner_id} (tupla ID/Nome)
 * e sulla resilienza del costruttore di fronte a tipi di dato inattesi.
 */
@RunWith(Parameterized.class)
public class ContattoConsegnaDTOTest {

/** Mappa di input simulata (risposta XML-RPC). */
    private Map<String, Object> in;
/** Mappa dei valori attesi dopo il parsing. Se {@code null}, è attesa un'eccezione. */
    private Map<String, Object> out;
	
/**
     * Genera i casi di test combinando diversi scenari di validità.
     * <p>
     * Scenari coperti:
     * <ol>
     * <li><b>Happy Path:</b> ID (Integer) e PartnerID (Array[2]) corretti.</li>
     * <li><b>Type Mismatch (Safe Parsing):</b> ID errato (String) o elementi interni al PartnerID errati. 
     * Il DTO deve gestire questi casi restituendo {@code Optional.empty()} senza lanciare eccezioni.</li>
     * <li><b>Malformed Data (Exception):</b> Campo {@code partner_id} nullo o array di lunghezza errata.
     * Questi sono errori strutturali che devono impedire la creazione dell'oggetto.</li>
     * </ol>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String partnerID = "partner_id";
		List<Object[]> tests = new ArrayList<>();
		
		//0 ID ok, partnerID ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); put(partnerID, new Object[] { 1 , "ID-001" } ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(partnerID, new Object[] { Optional.of(1) , Optional.of("ID-001") } ); }},
							} );
		
		//1 ID notOk, partnerID ok (id errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(partnerID, new Object[] { "1" , "ID-001" } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(partnerID, new Object[] { Optional.empty() , Optional.of("ID-001") } ); }},
							} );

		//2 ID null, partnerID ok (name errato)
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(partnerID, new Object[] { 1 , 1 } ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(partnerID, new Object[] { Optional.of(1) , Optional.empty() } ); }},
							} );
		
		//3 ID ok, partnerID null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(partnerID, null ); }},
				null
							} );

		
		//4 ID notOk, partnerID notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(partnerID, new Object[] { 1 } ); }},
				null
							} );

		
		
		return tests;
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Mappa dati input.
     * @param out Mappa dati attesi (o null).
     */
    public ContattoConsegnaDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Logica di verifica:
     * <ul>
     * <li>Se ci si aspetta successo ({@code out != null}): Verifica che il DTO non sia nullo e che i campi
     * (ID e PartnerID) contengano esattamente i valori attesi (inclusi gli Optional vuoti).</li>
     * <li>Se ci si aspetta errore ({@code out == null}): Verifica che il costruttore lanci un'eccezione
     * e che tale eccezione sia giustificata dal fatto che {@code partner_id} non rispetta la struttura Array[2].</li>
     * </ul>
     */
    @Test
    public void Test() {
		final String ID = "id";
		final String partnerID = "partner_id";
		ContattoConsegnaDTO contcons = null;
		try {
			contcons = new ContattoConsegnaDTO(in);
			assertThat(contcons)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID));
			
			assertThat(contcons.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(contcons.getPartnerId())
					.isNotNull()
				    .isInstanceOfSatisfying(IdentifierDTO.class, id -> {
				        assertThat(id.getNum()).isEqualTo( ( (Object[])  out.get(partnerID))[0] );
				        assertThat(id.getName()).isEqualTo( ( (Object[])  out.get(partnerID))[1] );
				    });
		}catch(Exception e) {
			/* warehouseID 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( in.get(partnerID) )
					.matches(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
	
}
