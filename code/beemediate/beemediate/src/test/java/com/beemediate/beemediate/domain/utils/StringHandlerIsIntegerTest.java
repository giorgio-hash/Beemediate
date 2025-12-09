package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * testing MCDC del metodo <i>StringHandler.isInteger</i>.
 * <ul><li>Decisione 1: if(str == null || str.length()==0)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>str == null</th>
 * <th>str.length() == 0</th>
 * <th>esito dec.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T0</td> <td>F</td> <td>F</td> <td>false</td> <td>(prosegue)</td> <td>str="0"</td>
 * </tr>
 * <tr>
 * <td>T1</td> <td>T</td> <td>-</td> <td>true</td> <td>false</td> <td>str=null</td>
 * </tr>
 * <tr>
 * <td>T2</td> <td>F</td> <td>T</td> <td>true</td> <td>false</td> <td>str=""</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 2: if(str.length() == 1)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>(str.length() == 1)</th>
 * <th>esito dec.</th>
 * <th>esito metodo</th>
 * <th>inputs</th>
 * </tr>
 * <tr>
 * <td>T3</td> <td>T</td> <td>true</td> <td>(entra 'then')</td> <td>str="0"</td>
 * </tr>
 * <tr>
 * <td>T4</td> <td>F</td> <td>false</td> <td>(entra 'else')</td> <td>str="10"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 3: return isDigit(str.charAt(0),false)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>isDigit(str.charAt(0),false)</th>
 * <th>esito dec.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T5</td> <td>F</td> <td>false</td> <td>false</td> <td>str="a"</td>
 * </tr>
 * <tr>
 * <td>T6</td> <td>T</td> <td>true</td> <td>true</td> <td>str="0"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 4: if ( !isDigit( str.charAt(i), i==0 ) )
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>!isDigit( str.charAt(i), i==0 )</th>
 * <th>esito dec.</th>
 * <th>esito metodo</th>
 * <th>inputs</th>
 * </tr>
 * <tr>
 * <td>T7</td> <td>F</td> <td>false</td> <td>true</td> <td>str="10"</td>
 * </tr>
 * <tr>
 * <td>T8</td> <td>T</td> <td>true</td> <td>false</td> <td>str="0.1"</td>
 * </tr>
 * </table>
 * </p></li>
 * </ul>
 */
public class StringHandlerIsIntegerTest {
	
	//if(str == null || str.length()==0)
	/**CASE		(str == null || str.length()==0)	|	esito dec.	| esito metodo	|	esito
	 * 	T0			F				F				|	false		|	(prosegue)	|	str="0"
	 * 	T1			T				-				|	true		|	false		|	str=null
	 * 	T2			F				T				|	true		|	false		|	str=""
	 */
	
	//if(str.length() == 1)
	/**CASE		(str.length() == 1)	|	esito dec.	|	esito metodo	|	inputs
	 * 	T3			T				|	true		|	(entra 'then')	|	str="0"
	 * 	T4			F				|	false		|	(entra	'else')	|	str="10"
	 */
	
	//return isDigit(str.charAt(0),false)
	/**CASE		isDigit(str.charAt(0),false)	|	esito dec.	|	esito metodo	|	input
	 * 	T5			F							|	false		|	false			|	str="a"
	 * 	T6			T							|	true		|	true			|	str="0"
	 */

	//if ( !isDigit( str.charAt(i), i==0 ) )
	/**CASE	!isDigit( str.charAt(i), i==0 )	|	esito dec.	|	esito metodo	|	inputs
	 * 	T7			F						|	false		|	true			|	str="10"
	 * 	T8			T						|	true		|	false			|	str="0.1"
	 */

	/**
	 * Test del caso T0, T3, T6
	 */
	@Test
	public void test_MCDC_T0_T3_T6() {
		assertTrue("Singola cifra è un integer (T0,T6)", StringHandler.isInteger("0"));
	}

	/**
	 * Test del caso T1
	 */
	@Test
	public void test_MCDC_T1() {
		assertFalse("input null non vale come Integer", StringHandler.isInteger(null));
	}
	
		/**
	 * Test del caso T2
	 */
	@Test
	public void test_MCDC_T2() {
		assertFalse("stringa vuota non vale come integer", StringHandler.isInteger(""));
	}
	
		/**
	 * Test del caso T4, T7
	 */
	@Test
	public void test_MCDC_T4_T7() {
		assertTrue("String con numeri a più cifre non ha leading zero nè caratteri non-digit", StringHandler.isInteger("10"));
	}
	
	/**
	 * Test del caso T5
	 */
	@Test
	public void test_MCDC_T5() {
		assertFalse("Singolo char non-digit non è Integer", StringHandler.isInteger("a"));
	}
	
	/**
	 * Test del caso T8
	 */
	@Test
	public void test_MCDC_T8() {
		assertFalse("String con length>1 contenente leading-zero non va bene", StringHandler.isInteger("0.1"));
	}
}
