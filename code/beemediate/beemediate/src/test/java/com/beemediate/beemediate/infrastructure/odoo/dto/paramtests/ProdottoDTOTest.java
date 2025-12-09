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

import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;

/**
 * Test parametrico per la classe {@link ProdottoDTO}.
 * <p>
 * Verifica la corretta deserializzazione dei dati del prodotto, con particolare attenzione 
 * al campo {@code seller_ids}. In Odoo, questo campo rappresenta una relazione (spesso verso 
 * {@code product.supplierinfo}) e viene restituito via XML-RPC come un array di ID (interi o stringhe).
 * <p>
 * Il test controlla la robustezza del parsing:
 * <ul>
 * <li><b>Happy Path:</b> ID intero e array di Seller ID validi.</li>
 * <li><b>Safe Parsing:</b> Gestione di tipi non conformi (es. String al posto di Array per {@code seller_ids}),
 * che devono risultare in un {@code Optional.empty()} invece di un'eccezione.</li>
 * </ul>
 */
@RunWith(Parameterized.class)
public class ProdottoDTOTest {
	
/** Mappa di input simulata. */
    private Map<String, Object> in;
/** Mappa dei valori attesi. */
    private Map<String, Object> out;
	
/**
     * Definisce la matrice dei casi di test.
     * <p>
     * Scenari:
     * <ol>
     * <li><b>Valid:</b> ID (Integer) e SellerIds (Array di Object) presenti.</li>
     * <li><b>Invalid ID / Null Sellers:</b> ID errato (String), SellerIds nullo. Atteso: Empty.</li>
     * <li><b>Null ID / Invalid Sellers:</b> ID nullo, SellerIds errato (String invece di Array). Atteso: Empty.</li>
     * </ol>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		final String ID = "id";
		final String sellerIds = "seller_ids";
		List<Object[]> tests = new ArrayList<>();
		
		// id ok, ref ok
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(sellerIds, new Object[] { "2" }  ); }},
				new HashMap<>() {{ put(ID,Optional.of(1)); put(sellerIds, Optional.of( new Object[] { "2" } )); }},
							} );
		
		// id notOk, ref null
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 			put(sellerIds, null); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(sellerIds, Optional.empty()); }},
							} );
		
		// id null, ref notOk
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(sellerIds, "2" ); }},
				new HashMap<>() {{ put(ID,Optional.empty()); put(sellerIds, Optional.empty()); }},
							} );
		
		return tests;
		
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Mappa input.
     * @param out Mappa output atteso.
     */
    public ProdottoDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Verifica che:
     * <ul>
     * <li>Il DTO sia creato correttamente.</li>
     * <li>L'ID sia mappato correttamente (Presente o Vuoto).</li>
     * <li>Il campo {@code seller_ids} venga gestito correttamente: se presente, 
     * il contenuto dell'array viene verificato elemento per elemento.</li>
     * </ul>
     */
    @Test
    public void Test() {
		final String ID = "id";
		final String sellerIds = "seller_ids";
		ProdottoDTO prod = null;
		
			prod = new ProdottoDTO(in);
			assertThat(prod)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID));
			
			assertThat(prod.getId())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out.get(ID));
				});
			
			if(prod.getSellerIds().isPresent()) {
				Optional<Object[]> actual = prod.getSellerIds();
				Optional<Object[]> expected = (Optional<Object[]>)  out.get(sellerIds);
				assertThat(actual.get())
						.contains(expected.get());
			}else
				assertThat(prod.getSellerIds()).isEmpty();
	}

}
