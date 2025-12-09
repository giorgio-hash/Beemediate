package com.beemediate.beemediate.infrastructure.odoo.dto.paramtests;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

/**
 * Test parametrico per la classe {@link IdentifierDTO}.
 * <p>
 * Questa classe è fondamentale poiché {@link IdentifierDTO} rappresenta la struttura base 
 * per mappare le chiavi esterne (Many2One) di Odoo, che vengono restituite via XML-RPC come array 
 * di due elementi: {@code [Integer id, String display_name]}.
 * <p>
 * Il test verifica:
 * <ul>
 * <li><b>Resilienza sui tipi:</b> Se l'ID o il Nome non sono del tipo atteso (es. {@code null} o tipi errati), 
 * il DTO deve restituire {@code Optional.empty()} invece di rompersi.</li>
 * <li><b>Validazione strutturale:</b> Se l'input non è un array o ha una lunghezza diversa da 2, 
 * il costruttore deve fallire, segnalando un'anomalia grave nel protocollo.</li>
 * </ul>
 * <p>Schema MCDC-like degli input di test
 * <table border="1" cellpadding="5" cellspacing="0" style="border-collapse: collapse; font-family: monospace; text-align: center;">
    <thead>
        <tr style="background-color: #f2f2f2;">
            <th>CASE</th>
            <th>num</th>
            <th>name</th>
            <th>in!=null</th>
            <th>in.length==2</th>
            <th>ESITO</th>
        </tr>
    </thead>
    <tbody>
        <tr>
            <td>1</td>
            <td>null</td>
            <td></td>
            <td>true</td>
            <td>true</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>2</td>
            <td></td>
            <td>notOk</td>
            <td>true</td>
            <td>true</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>3</td>
            <td>notOk</td>
            <td>null</td>
            <td>true</td>
            <td>true</td>
            <td style="text-align: left;">ok</td>
        </tr>
        <tr>
            <td>4</td>
            <td></td>
            <td>-</td>
            <td>true</td>
            <td>false</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
        <tr>
            <td>5</td>
            <td>-</td>
            <td>-</td>
            <td>false</td>
            <td>.</td>
            <td style="text-align: left;">eccezione</td>
        </tr>
    </tbody>
</table></p>
 */
@RunWith(Parameterized.class)
public class IdentifierDTOTest {
	
/** Array di input simulato (la tupla Odoo). */
    private Object[] in;
/** Array di output atteso contenente due Optional ([Opt<Int>, Opt<String>]). Se null, attesa eccezione. */
    private Object[] out;
	
/**
     * Definisce i casi di test.
     * <p>
     * Scenari:
     * <ol>
     * <li><b>Case 1:</b> ID null, Nome valido. -> ID Empty, Nome Present.</li>
     * <li><b>Case 2:</b> ID valido, Nome tipo errato (Int). -> ID Present, Nome Empty.</li>
     * <li><b>Case 3:</b> ID tipo errato (String), Nome null. -> Entrambi Empty.</li>
     * <li><b>Case 4 (Strutturale):</b> Array troppo corto (lunghezza 1). -> Eccezione.</li>
     * <li><b>Case 5 (Strutturale):</b> Input null. -> Eccezione.</li>
     * </ol>
     *
     * @return Collezione di array [InputArray, ExpectedOutputArray].
     */
    @Parameters
	public static Collection<Object[]> parameters() {
		
		List<Object[]> tests = new ArrayList<Object[]>();
		
		/*
		 * CASE			num			name		in!=null	in.length==2	|ESITO
		 * 	1			null					true		true			|ok
		 * 	2						notOk		true		true			|ok
		 * 	3			notOk		null		true		true			|ok
		 * 	4						-			true		false			|eccezione
		 * 	5			-			-			false		.				|eccezione
		 * ***********************************************************************
		 * */
		
		//1
		tests.add(new Object[] {
				new Object[] { null,			"nome" },
				new Object[] { Optional.empty(),Optional.of("nome") },
		} );
		//2
		tests.add(new Object[] {
				new Object[] { 1,				1 },
				new Object[] { Optional.of(1),Optional.empty() },
		} );
		//3
		tests.add(new Object[] {
				new Object[] { "1",				null },
				new Object[] { Optional.empty(),Optional.empty() },
		} );
		//4
		tests.add(new Object[] {
				new Object[] { 1 },
				null
		} );
		//5
		tests.add(new Object[] {
				null,
				null
		} );
		
		
		return tests;
	}
	
/**
     * Costruttore del test parametrico.
     * @param in Array input.
     * @param out Array output atteso (o null).
     */
    public IdentifierDTOTest(Object[] in, Object[] out) {
		this.in = in;
		this.out = out;
	}
	
/**
     * Esegue il test di instanziazione.
     * <p>
     * Logica:
     * <ul>
     * <li><b>Successo atteso (out != null):</b> Verifica che {@code num} e {@code name} siano popolati 
     * correttamente secondo gli Optional definiti in {@code out}.</li>
     * <li><b>Fallimento atteso (out == null):</b> Verifica che venga lanciata un'eccezione e che questa sia 
     * coerente con i dati di input (input nullo, non array, o array di dimensione errata).</li>
     * </ul>
     */
    @Test
    public void Test() {
	
		final int num=0;
		final int name=1;
		
		IdentifierDTO ident = null;
		
		try {
			ident = new IdentifierDTO(in);
			
			assertThat(ident)
				.isNotNull()
				.hasNoNullFieldsOrProperties()
				.hasFieldOrPropertyWithValue("num", out[num])
				.hasFieldOrPropertyWithValue("name", out[name]);

			assertThat(ident.getNum())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out[num]);
				});
			
			assertThat(ident.getName())
				.isNotNull()
				.isInstanceOfSatisfying(Optional.class, o -> {
					assertEquals(o, out[name]);
				});
				
		}catch(Exception e) {
			/* L'input 
			 * - è null
			 * - non è istanza di Object[]
			 * - è istanza di Object[] ma non è sufficientemente grande
			 * */
			assertThat(in).satisfiesAnyOf(
				    o -> assertThat(o).isNull(),
				    o -> assertThat(o).isNotInstanceOf(Object[].class),
				    o -> assertThat(o).isInstanceOfSatisfying(Object[].class, a -> assertThat(a.length).isNotEqualTo(2))
				);
		}
	}

}
