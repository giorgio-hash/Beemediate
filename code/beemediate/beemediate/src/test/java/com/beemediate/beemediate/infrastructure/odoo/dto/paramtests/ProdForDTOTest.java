package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;

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

import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;
import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoFornitoreDTO;

/**
 * Test parametrico per la classe {@link ProdottoFornitoreDTO}.
 * <p>
 * Verifica la logica di deserializzazione dei dati relativi alle informazioni di fornitura (Supplier Info).
 * Questo DTO è critico perché contiene tre chiavi esterne (Many2One) che devono essere tutte valide:
 * <ul>
 * <li>{@code product_id} (Prodotto)</li>
 * <li>{@code partner_id} (Fornitore)</li>
 * <li>{@code product_uom_id} (Unità di misura)</li>
 * </ul>
 * Il test controlla che l'oggetto venga istanziato solo se la struttura di queste chiavi è corretta,
 * altrimenti deve fallire in sicurezza.
 * <p>Lo schema degli input è riassumibile nel seguente modo<table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center; font-size: 12px;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASO</th>
            <th>id</th>
            <th>productId</th>
            <th>sequence</th>
            <th>productName</th>
            <th>productCode</th>
            <th>partnerId</th>
            <th>productUomId</th>
            <th>ESITO</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>0</td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>1</td>
            <td></td>
            <td>null</td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>2</td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td>null</td>
            <td></td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>3</td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td></td>
            <td>null</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>4</td>
            <td>null</td>
            <td></td>
            <td>null</td>
            <td>null</td>
            <td>null</td>
            <td></td>
            <td></td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>5</td>
            <td>notOk</td>
            <td></td>
            <td>notOk</td>
            <td>notOk</td>
            <td>notOk</td>
            <td></td>
            <td></td>
            <td style="text-align: left;">ok</td>
        </tr>
    </tbody>
</table></p>
 */
@RunWith(Parameterized.class)
public class ProdForDTOTest {
	
/** Mappa di input simulata. */
    private Map<String, Object> in;
/** Mappa dei valori attesi. Se {@code null}, è attesa un'eccezione. */
    private Map<String, Object> out;
	
/**
     * Definisce la matrice dei casi di test.
     * <p>
     * Scenari coperti:
     * <ol>
     * <li><b>Happy Path (Case 0):</b> Tutti i campi presenti e corretti.</li>
     * <li><b>Missing/Invalid References (Case 1, 2, 3):</b> Uno dei campi relazionali (`product_id`, `partner_id`, `product_uom_id`) 
     * è nullo. Poiché questi campi sono essenziali per identificare il record, ci si aspetta un fallimento (Eccezione).</li>
     * <li><b>Safe Parsing (Case 4, 5):</b> Campi semplici (`sequence`, `product_name`) nulli o di tipo errato. 
     * In questo caso il DTO deve essere resiliente e popolarli come {@code Optional.empty()}, permettendo la creazione dell'oggetto.</li>
     * </ol>
     *
     * @return Collezione di array [Input, ExpectedOutput].
     */
	@Parameters
	public static Collection<Object[]> parameters() {
		/*
	CASO	 		id				productId		sequence		productName		productCode		partnerId		productUomId	|	ESITO
		0																															|	ok
		1							null																							|	eccezione
		2																							null							|	eccezione
		3																											null			|	eccezione
		4			null							null			null			null											|	ok
		5			notOk							notOk			notOk			notOk											|	ok
		************************************************************************************ 
		*/
		
		final String ID = "id";
		final String productId = "product_id";
		final String partnerId = "partner_id";
		final String productUomId = "product_uom_id";
		final String sequence = "sequence";
		final String productName = "product_name";
		final String productCode = "product_code";
		
		
		List<Object[]> tests = new ArrayList<>();
		
		//0 
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				new HashMap<>() {{ put(ID,Optional.of(1)); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.of(1));	put(productName, Optional.of("prod001"));	put(productCode, Optional.of("prod001"));	}},
							} );
		//1
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, null);								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//2
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, null);								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//3
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,1); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, null);							put(sequence, 1);				put(productName, "prod001");				put(productCode, "prod001");				}},
				null
							} );
		//4
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,null); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, null);				put(productName, null);				put(productCode, null);				}},
				new HashMap<>() {{ put(ID,Optional.empty()); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.empty());	put(productName, Optional.empty());	put(productCode, Optional.empty());	}},
							} );		
		//5
		tests.add( new Object[] { 
				new HashMap<>() {{ put(ID,"1"); 				put(productId, new Object[] { 1, "PROD001" });								put(partnerId, new Object[] { 1, "PROD001" });								put(productUomId, new Object[] { 1, "PROD001" });							put(sequence, "1");				put(productName, 1);				put(productCode, 1);				}},
				new HashMap<>() {{ put(ID,Optional.empty()); 	put(productId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(partnerId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(productUomId, new Object[] { Optional.of(1), Optional.of("PROD001") });	put(sequence, Optional.empty());	put(productName, Optional.empty());	put(productCode, Optional.empty());	}},
							} );
		
		return tests;
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Mappa input.
     * @param out Mappa output atteso.
     */
    public ProdForDTOTest(Map<String, Object> in, Map<String, Object> out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Logica di verifica:
     * <ul>
     * <li><b>Caso Successo (out != null):</b> Verifica che tutti i campi siano popolati correttamente. 
     * Controlla i valori semplici (es. sequence) e naviga all'interno dei DTO annidati ({@link IdentifierDTO}) 
     * per verificare ID e Nome.</li>
     * <li><b>Caso Errore (out == null):</b> Verifica che venga lanciata un'eccezione e che la causa sia 
     * strutturale (uno dei campi ID relazionali non è un array valido).</li>
     * </ul>
     */
    @Test
    public void test() {
		final String ID = "id";
		final String productId = "product_id";
		final String partnerId = "partner_id";
		final String productUomId = "product_uom_id";
		final String sequence = "sequence";
		final String productName = "product_name";
		final String productCode = "product_code";
		
		
		ProdottoFornitoreDTO prodF = null;
		try {
			prodF = new ProdottoFornitoreDTO(in);
			assertThat(prodF)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("id", out.get(ID))
				.hasFieldOrPropertyWithValue("sequence", out.get(sequence))
				.hasFieldOrPropertyWithValue("productName", out.get(productName))
				.hasFieldOrPropertyWithValue("productCode", out.get(productCode))
			    .extracting(
			        ProdottoFornitoreDTO::getId,
			        ProdottoFornitoreDTO::getSequence,
			        ProdottoFornitoreDTO::getProductName,
			        ProdottoFornitoreDTO::getProductCode
			    )
			    .containsExactly(
			    		out.get(ID),
			    		out.get(sequence),
			    		out.get(productName),
			    		out.get(productName)
			    		);
			
			assertThat(prodF.getProductId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(productId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(productId))[1] );
			    });
			
			assertThat(prodF.getPartnerId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(partnerId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(partnerId))[1] );
			    });
			
			assertThat(prodF.getProductUomId())
				.isNotNull()
			    .isInstanceOfSatisfying(IdentifierDTO.class, o -> {
			        assertThat(o.getNum()).isEqualTo( ( (Object[])  out.get(productUomId))[0] );
			        assertThat(o.getName()).isEqualTo( ( (Object[])  out.get(productUomId))[1] );
			    });
			

		}catch(Exception e) {
			/* Almeno uno tra i campi productID, partnerId e productUomId : 
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat( Arrays.asList( new Object[] { in.get(productId),in.get(partnerId), in.get(productUomId) }  ) )
		    				.anyMatch(o -> !(o instanceof Object[] && ((Object[]) o).length == 2));
		}
	}
}
