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

import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;

/**
 * Test parametrico per la classe {@link FornitoreDTO}.
 * <p>
 * Verifica la logica di deserializzazione "safe" dei dati provenienti da Odoo.
 * Il test copre combinazioni di input validi, nulli e di tipo errato per i tre campi principali:
 * <ul>
 * <li><b>ID</b> (atteso Integer)</li>
 * <li><b>Name</b> (atteso String)</li>
 * <li><b>Ref</b> / Codice Azienda (atteso String)</li>
 * </ul>
 * L'obiettivo è assicurare che il DTO non sollevi eccezioni in caso di dati sporchi, 
 * ma popoli correttamente gli {@link Optional}.
 */
@RunWith(Parameterized.class)
public class FornitoreDTOTest {
	
/** Mappa di input simulata (risposta XML-RPC). */
    private Map<String, Object> in;
/** Mappa dei valori attesi (Optional popolati o vuoti). */
    private Map<String, Object> out;
	
/**
     * Genera la suite di casi di test.
     * <p>
     * I casi sono selezionati per coprire diverse permutazioni di validità tra i tre campi, 
     * evitando ridondanze eccessive ma garantendo che ogni campo venga testato sia in scenario di successo 
     * che di fallimento (null o type mismatch).
     * <p>
     * Esempi di scenari:
     * <ul>
     * <li><b>Case 3:</b> ID nullo, Nome tipo errato (Int), Ref valido. -> Solo Ref popolato.</li>
     * <li><b>Case 5:</b> ID tipo errato (String), Nome valido, Ref nullo. -> Solo Nome popolato.</li>
     * <li><b>Case 6:</b> ID valido, Nome nullo, Ref tipo errato (Int). -> Solo ID popolato.</li>
     * </ul>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
	@Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String nome = "name";
		final String codiceAzienda = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		/*
		 * 
		 * Voglio che i parametri ricevano input: ok, notOk, null.
		 * I parametri sono scorrelati tra loro.
		 * 
		CASE		id			name			ref
			0											<--escludo perchè ridondante
			1		notOk								<--escludo perchè ridondante
			2					notOK					<--escludo perchè ridondante
			3		null		notOk			
			4									notOk   <--escludo perchè ridondante
			5		notOK						null
			6					null			notOk	
			7		notOK		notOk			notOK	<--escludo perchè ridondante
		 * */
		
		//3
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(nome, 2); 			put(codiceAzienda, "2"); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(nome, Optional.empty()); put(codiceAzienda, Optional.of("2")); }},
							} );
		//5
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(nome, "2"); 			put(codiceAzienda, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(nome, Optional.of("2")); put(codiceAzienda, Optional.empty()); }},
							} );
		//6
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(nome, null); 			put(codiceAzienda, 2); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(nome, Optional.empty()); put(codiceAzienda, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Mappa input.
     * @param out Mappa output atteso.
     */
    public FornitoreDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione e validazione dei campi.
     * <p>
     * Verifica che:
     * <ul>
     * <li>L'oggetto {@link FornitoreDTO} venga creato correttamente.</li>
     * <li>Tutti i campi (ID, Nome, CodiceAzienda) corrispondano esattamente allo stato 
     * (presente/vuoto) e al valore definito nella mappa di output atteso.</li>
     * </ul>
     */
    @Test
    public void Test() {
		final String ID = "id";
		final String nome="name";
		final String codiceAzienda = "ref";
		FornitoreDTO forn = null;
		
			forn = new FornitoreDTO(in);
			assertThat(forn)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("codiceAzienda", out.get(codiceAzienda))
				.hasFieldOrPropertyWithValue("name", out.get(nome));
			
			assertThat(forn.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			assertThat(forn.getCodiceAzienda())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(codiceAzienda));
			});
			
			assertThat(forn.getName())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, o -> {
				assertEquals(o, out.get(nome));
			});
	}

}
