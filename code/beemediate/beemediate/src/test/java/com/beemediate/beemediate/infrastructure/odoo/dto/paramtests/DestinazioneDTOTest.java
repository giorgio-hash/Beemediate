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

import com.beemediate.beemediate.infrastructure.odoo.dto.DestinazioneDTO;

/**
 * Test parametrico per la classe {@link DestinazioneDTO}.
 * <p>
 * Verifica la logica di costruzione del DTO a partire da una mappa di valori (stile XML-RPC).
 * Il test si concentra sulla robustezza del parsing:
 * <ul>
 * <li>Se i dati sono conformi (ID intero, Codice stringa), vengono mappati correttamente.</li>
 * <li>Se i dati sono nulli o di tipo errato, il DTO deve gestire la situazione restituendo 
 * un {@link Optional#empty()} invece di lanciare eccezioni di cast.</li>
 * </ul>
 */
@RunWith(Parameterized.class)
public class DestinazioneDTOTest {
	
/** Mappa di input simulata. */
    private Map<String, Object> in;
/** Mappa dei valori attesi (Optional popolati o vuoti). */
    private Map<String, Object> out;
	
/**
     * Definisce i casi di test.
     * <p>
     * Scenari:
     * <ol>
     * <li><b>Happy Path:</b> ID (Integer) e Ref (String) presenti e corretti.</li>
     * <li><b>Safe Parsing 1:</b> ID di tipo errato (String) e Ref nullo. 
     * Atteso: Entrambi {@code Optional.empty()}.</li>
     * <li><b>Safe Parsing 2:</b> ID nullo e Ref di tipo errato (Integer). 
     * Atteso: Entrambi {@code Optional.empty()}.</li>
     * </ol>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String codiceDestinazione = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(codiceDestinazione, "2"); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(codiceDestinazione, Optional.of("2")); }},
							} );
		
		// id notOk, ref null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(codiceDestinazione, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(codiceDestinazione, Optional.empty()); }},
							} );
		
		// id null, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(codiceDestinazione, 2); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(codiceDestinazione, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Mappa input.
     * @param out Mappa output atteso.
     */
    public DestinazioneDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Verifica che:
     * <ul>
     * <li>L'oggetto {@link DestinazioneDTO} venga creato correttamente (non null).</li>
     * <li>Il campo {@code id} corrisponda all'Optional atteso (valore o empty).</li>
     * <li>Il campo {@code codiceDestinazione} corrisponda all'Optional atteso (valore o empty).</li>
     * </ul>
     */
    @Test
    public void Test() {
		final String ID = "id";
		final String codiceDestinazione = "ref";
		DestinazioneDTO dest = null;
		
			dest = new DestinazioneDTO(in);
			assertThat(dest)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("codiceDestinazione", out.get(codiceDestinazione));
			
			assertThat(dest.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			assertThat(dest.getCodiceDestinazione())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(codiceDestinazione));
			});
	}

}
