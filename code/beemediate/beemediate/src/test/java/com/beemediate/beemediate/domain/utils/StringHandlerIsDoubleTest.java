package com.beemediate.beemediate.domain.utils;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import org.junit.Test;

public class StringHandlerIsDoubleTest {

	//if(str == null || str.length()<3 || str.charAt(str.length()-1) == comma || str.charAt(0) == comma)
	/**CASE		str == null  str.length()<3  str.charAt(str.length()-1)==comma   	str.charAt(0)==comma	|	esito deci. | esito metodo 	| input
	 * 	T0			F			F					F									F					|	false		| (prosegue)   	| str="1.2"
	 * 	T1			T			-																			|	true		|	false		| str=null
	 * 	T2			F			T																			|	true		|	false		| str="10"
	 * 	T3			F			F					T														|	true		|	false		| str="00."
	 * 	T4			F			F					F									T					|	true		|	false		| str=".01"
	 */
	
	//if ( str.charAt(1) != '.' && !isDigit(str.charAt(0),true) )
	/**CASE		str.charAt(1) != '.'		!isDigit(str.charAt(0),true)	|	esito deci.	|	esito metodo	|	input
	 * 	T5			F								-						|	false		|	(prosegue)		|	str="1.2"
	 * 	T6			T								T						|	true		|	false			|	str="00.1"
	 */
	
	
	//if( !isDigit(str.charAt(i),false) )
	/**CASE		!isDigit(str.charAt(i),false)	|	esito deci.		|	esito metodo			|	inputs
	 * 	T7			T							|	true			|	(va a sottodecisione)	|	str="1.2"
	 * 	T8			F							|	false			|	(non va mai a sottod.)	|	str="100"
	 */
	
	
	//if (str.charAt(i) == comma)
	/**CASE		str.charAt(i)==comma	|	esito deci.	|	esito metodo	|	inputs
	 * 	T9			T					|	true		|	(prosegue)		|	str="1.2"
	 * 	T10			F					|	false		|	false			|	str="1a1"
	 */
	
	//return numOfCommas==1;
	/**CASE		numOfCommas==1		|	esito deci.	|	esito metodo	|	inputs
	 * 	T11			T				|	true		|	true			|	str="1.2"
	 * 	T12			F				|	false		|	false			|	str="100"
	 */
	
	@Test
	public void test_MCDC_T0_T5_T7_T9_T11() {
		assertTrue("Happy path: numero con 'punto' virgola mobile ( T0, T5, T7, T9, T11)", StringHandler.isDouble("1.2"));
	}
	
	@Test
	public void test_MCDC_T1() {
		assertFalse("test T1 str=null", StringHandler.isDouble(null));
	}
	
	@Test
	public void test_MCDC_T2() {
		assertFalse("test T2 str troppo corto (length<3)", StringHandler.isDouble("10"));
	}
	
	@Test
	public void test_MCDC_T3() {
		assertFalse("test T3 str ha dot alla fine", StringHandler.isDouble("00."));
	}
	
	@Test
	public void test_MCDC_T4() {
		assertFalse("test T4 str ha dot all'inizio", StringHandler.isDouble(".01"));
	}
	
	@Test
	public void test_MCDC_T10() {
		assertFalse("test str contiene carattere non-digit e non '.' (T10)", StringHandler.isDouble("1a1"));
	}
	
	@Test
	public void test_MCDC_T6() {
		assertFalse("test str contiene leading zero per parte intera a più di una cifra (T6)", StringHandler.isDouble("00.1"));
	}
	
	@Test
	public void test_MCDC_T8_T12() {
		assertFalse("test str è un intero a 3 cifre (T8, T12)", StringHandler.isDouble("100"));
	}
}