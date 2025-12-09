package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * Test di unità per StringHandler.isDigit(char, boolean).
 *
 * Scopo:
 * Verificare il comportamento del metodo isDigit che determina se un carattere è una cifra decimale
 * valida in funzione di un flag booleano che influisce sul trattamento del carattere '0'.
 *
 * Partition testing applicato:
 * - Classe "cifre non nulle"  : caratteri '1'..'9' (atteso: true).
 * - Classe "zero"             : carattere '0' (comportamento dipendente dal flag).
 * - Classi "non-cifre"       : caratteri al di fuori dell'intervallo '0'..'9' (es. '/' e '{') (atteso: false).
 *
 * Per ogni classe di equivalenza è stato scelto un rappresentante (es. '/', '0', '1'..'9', '{')
 * al fine di coprire i casi rilevanti e dimostrare le regole di validazione senza testare
 * ogni possibile carattere. In particolare il flag booleano viene usato per distinguere i due
 * sotto-domini relativi al trattamento dello zero (zero ammesso vs zero escluso).
 */
public class StringHandlerIsDigitTest {

	
	/**
 * Test: comportamento quando lo zero è escluso (flag = true).
 *
 * Obiettivo del test:
 * - Verificare che i caratteri non-cifra (rappresentati da '/') restituiscano false.
 * - Verificare che '0' sia considerato non valido quando il flag indica che lo zero è escluso.
 * - Verificare che le cifre '1'..'9' siano considerate valide.
 * - Verificare che un carattere non-cifra oltre la gamma (rappresentato da '{') restituisca false.
 *
 * Nota sul partition testing:
 * Sono coperte le partizioni principali: non-cifre (valori sotto e sopra l'intervallo),
 * zero (caso speciale) e cifre non-nulle.
 */
	@Test
	public void testInput_whenNonZero() {
		
		assertFalse(StringHandler.isDigit('/', true));
		assertFalse(StringHandler.isDigit('0', true));
		assertTrue(StringHandler.isDigit('1', true));
		assertTrue(StringHandler.isDigit('2', true));
		assertTrue(StringHandler.isDigit('3', true));
		assertTrue(StringHandler.isDigit('4', true));
		assertTrue(StringHandler.isDigit('5', true));
		assertTrue(StringHandler.isDigit('6', true));
		assertTrue(StringHandler.isDigit('7', true));
		assertTrue(StringHandler.isDigit('8', true));
		assertTrue(StringHandler.isDigit('9', true));
		assertFalse(StringHandler.isDigit('{', true));
	}
	
	/**
 * Test: comportamento quando lo zero è ammesso (flag = false).
 *
 * Obiettivo del test:
 * - Verificare che i caratteri non-cifra (rappresentati da '/') restituiscano false.
 * - Verificare che '0' sia considerato valido quando il flag indica che lo zero è ammesso.
 * - Verificare che le cifre '1'..'9' siano considerate valide.
 * - Verificare che un carattere non-cifra oltre la gamma (rappresentato da '{') restituisca false.
 *
 * Nota sul partition testing:
 * Anche in questo caso si utilizzano rappresentanti per le stesse classi di equivalenza
 * per evidenziare il comportamento differente relativo alla partizione "zero".
 */
	@Test
	public void testInput_whenCanBeZero() {
		
		assertFalse(StringHandler.isDigit('/', false));
		assertTrue(StringHandler.isDigit('0', false));
		assertTrue(StringHandler.isDigit('1', false));
		assertTrue(StringHandler.isDigit('2', false));
		assertTrue(StringHandler.isDigit('3', false));
		assertTrue(StringHandler.isDigit('4', false));
		assertTrue(StringHandler.isDigit('5', false));
		assertTrue(StringHandler.isDigit('6', false));
		assertTrue(StringHandler.isDigit('7', false));
		assertTrue(StringHandler.isDigit('8', false));
		assertTrue(StringHandler.isDigit('9', false));
		assertFalse(StringHandler.isDigit('{', false));
	}
}
