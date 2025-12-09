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

import com.beemediate.beemediate.infrastructure.odoo.dto.CompagniaDTO;

/**
 * Test parametrico per la classe {@link CompagniaDTO}.
 * <p>
 * Verifica la logica di parsing "safe" del costruttore a partire da una Mappa generica.
 * Il test copre quattro scenari combinatori per verificare che:
 * <ul>
 * <li>Se i tipi di dato sono corretti (Integer per ID, String per Ref), i valori vengono popolati.</li>
 * <li>Se i tipi di dato sono errati (Type Mismatch), il DTO restituisce {@link Optional#empty()} 
 * invece di lanciare eccezioni di cast.</li>
 * </ul>
 */
@RunWith(Parameterized.class)
public class CompagniaDTOTest {
	
/** Mappa di input con i dati grezzi simulati da Odoo. */
    private Map<String, Object> in;
/** Mappa contenente gli oggetti {@link Optional} attesi dopo il parsing. */
    private Map<String, Object> out;
	
/**
     * Definisce la matrice dei casi di test.
     * <p>
     * Le chiavi utilizzate sono:
     * <ul>
     * <li>{@code id}: Atteso Integer.</li>
     * <li>{@code ref} (companyRegistry): Atteso String.</li>
     * </ul>
     * Casi testati:
     * <ol>
     * <li>ID ok, Ref ok -> Entrambi presenti.</li>
     * <li>ID errato (String), Ref ok -> ID Empty, Ref Presente.</li>
     * <li>ID ok, Ref errato (Integer) -> ID Presente, Ref Empty.</li>
     * <li>Entrambi errati -> Entrambi Empty.</li>
     * </ol>
     *
     * @return Collezione di array contenenti input e output atteso.
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String companyRegistry = "ref";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(companyRegistry, "2"); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(companyRegistry, Optional.of("2")); }},
							} );
		
		// id notOk, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(companyRegistry, "2"); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(companyRegistry, Optional.of("2")); }},
							} );
		
		// id ok, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(companyRegistry, 2); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(companyRegistry, Optional.empty()); }},
							} );
		
		// id notOk, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(companyRegistry, 2); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(companyRegistry, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
/**
     * Costruttore del test parametrico.
     *
     * @param in mappa dati in ingresso.
     * @param out mappa dati attesi.
     */
    public CompagniaDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Verifica che:
     * <ul>
     * <li>L'oggetto venga creato (non null).</li>
     * <li>I campi corrispondano esattamente agli {@link Optional} definiti nella mappa {@code out}.</li>
     * </ul>
     */
    @Test
    public void Test() {
		final String ID = "id";
		final String companyRegistry = "ref";
		CompagniaDTO comp = null;
		
			comp = new CompagniaDTO(in);
			assertThat(comp)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("companyRegistry", out.get(companyRegistry));
			
			assertThat(comp.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, id -> {
					assertEquals(id, out.get(ID));
				});
			
			assertThat(comp.getCompanyRegistry())
			.isNotNull()
			.isInstanceOfSatisfying(Optional.class, id -> {
				assertEquals(id, out.get(companyRegistry));
			});
	}

}
