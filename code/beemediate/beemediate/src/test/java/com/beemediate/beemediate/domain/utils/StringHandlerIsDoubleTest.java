package com.beemediate.beemediate.domain.utils;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import org.junit.Test;

/**
 * testing MCDC del metodo <i>StringHandler.isDouble</i>.
 * <ul><li>Decisione 1: if(str == null || str.length()<3 || str.charAt(str.length()-1) == comma || str.charAt(0) == comma)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>str == null</th>
 * <th>str.length() &lt; 3</th>
 * <th>str.charAt(str.length()-1) == comma</th>
 * <th>str.charAt(0) == comma</th>
 * <th>esito deci.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T0</td> <td>F</td> <td>F</td> <td>F</td> <td>F</td> <td>false</td> <td>(prosegue)</td> <td>str="1.2"</td>
 * </tr>
 * <tr>
 * <td>T1</td> <td>T</td> <td>-</td> <td>-</td> <td>-</td> <td>true</td> <td>false</td> <td>str=null</td>
 * </tr>
 * <tr>
 * <td>T2</td> <td>F</td> <td>T</td> <td>-</td> <td>-</td> <td>true</td> <td>false</td> <td>str="10"</td>
 * </tr>
 * <tr>
 * <td>T3</td> <td>F</td> <td>F</td> <td>T</td> <td>-</td> <td>true</td> <td>false</td> <td>str="00."</td>
 * </tr>
 * <tr>
 * <td>T4</td> <td>F</td> <td>F</td> <td>F</td> <td>T</td> <td>true</td> <td>false</td> <td>str=".01"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 2: if ( str.charAt(1) != '.' && !isDigit(str.charAt(0),true) )
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>str.charAt(1) != '.'</th>
 * <th>!isDigit(str.charAt(0),true)</th>
 * <th>esito deci.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T5</td> <td>F</td> <td>-</td> <td>false</td> <td>(prosegue)</td> <td>str="1.2"</td>
 * </tr>
 * <tr>
 * <td>T6</td> <td>T</td> <td>T</td> <td>true</td> <td>false</td> <td>str="00.1"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 3: if( !isDigit(str.charAt(i),false) )
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>!isDigit(str.charAt(i),false)</th>
 * <th>esito deci.</th>
 * <th>esito metodo</th>
 * <th>inputs</th>
 * </tr>
 * <tr>
 * <td>T7</td> <td>T</td> <td>true</td> <td>(va a sottodecisione)</td> <td>str="1.2"</td>
 * </tr>
 * <tr>
 * <td>T8</td> <td>F</td> <td>false</td> <td>(non va mai a sottod.)</td> <td>str="100"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 4: if (str.charAt(i) == comma)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>str.charAt(i)==comma</th>
 * <th>esito deci.</th>
 * <th>esito metodo</th>
 * <th>inputs</th>
 * </tr>
 * <tr>
 * <td>T9</td> <td>T</td> <td>true</td> <td>(prosegue)</td> <td>str="1.2"</td>
 * </tr>
 * <tr>
 * <td>T10</td> <td>F</td> <td>false</td> <td>false</td> <td>str="1a1"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 5: return numOfCommas==1;
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>numOfCommas==1</th>
 * <th>esito deci.</th>
 * <th>esito metodo</th>
 * <th>inputs</th>
 * </tr>
 * <tr>
 * <td>T11</td> <td>T</td> <td>true</td> <td>true</td> <td>str="1.2"</td>
 * </tr>
 * <tr>
 * <td>T12</td> <td>F</td> <td>false</td> <td>false</td> <td>str="100"</td>
 * </tr>
 * </table>
 * </p></li>
 * </ul>
 */
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
	
	/**
	 * Test del caso T0,T5,T7,T9,T11
	 */
	@Test
	public void test_MCDC_T0_T5_T7_T9_T11() {
		assertTrue("Happy path: numero con 'punto' virgola mobile ( T0, T5, T7, T9, T11)", StringHandler.isDouble("1.2"));
	}
	
		/**
	 * Test del caso T1
	 */
	@Test
	public void test_MCDC_T1() {
		assertFalse("test T1 str=null", StringHandler.isDouble(null));
	}
	
		/**
	 * Test del caso T2
	 */
	@Test
	public void test_MCDC_T2() {
		assertFalse("test T2 str troppo corto (length<3)", StringHandler.isDouble("10"));
	}
	
		/**
	 * Test del caso T3
	 */
	@Test
	public void test_MCDC_T3() {
		assertFalse("test T3 str ha dot alla fine", StringHandler.isDouble("00."));
	}
	
		/**
	 * Test del caso T4
	 */
	@Test
	public void test_MCDC_T4() {
		assertFalse("test T4 str ha dot all'inizio", StringHandler.isDouble(".01"));
	}
	
		/**
	 * Test del caso T10
	 */
	@Test
	public void test_MCDC_T10() {
		assertFalse("test str contiene carattere non-digit e non '.' (T10)", StringHandler.isDouble("1a1"));
	}
	
		/**
	 * Test del caso T6
	 */
	@Test
	public void test_MCDC_T6() {
		assertFalse("test str contiene leading zero per parte intera a più di una cifra (T6)", StringHandler.isDouble("00.1"));
	}
	
		/**
	 * Test del caso T8, T12
	 */
	@Test
	public void test_MCDC_T8_T12() {
		assertFalse("test str è un intero a 3 cifre (T8, T12)", StringHandler.isDouble("100"));
	}
}