package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class StringHandlerIsInteger {
	
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

	@Test
	public void test_MCDC_T0_T3_T6() {
		assertTrue("Singola cifra è un integer (T0,T6)", StringHandler.isInteger("0"));
	}

	@Test
	public void test_MCDC_T1() {
		assertFalse("input null non vale come Integer", StringHandler.isInteger(null));
	}
	
	@Test
	public void test_MCDC_T2() {
		assertFalse("stringa vuota non vale come integer", StringHandler.isInteger(""));
	}
	
	@Test
	public void test_MCDC_T4_T7() {
		assertTrue("String con numeri a più cifre non ha leading zero nè caratteri non-digit", StringHandler.isInteger("10"));
	}
	
	@Test
	public void test_MCDC_T5() {
		assertFalse("Singolo char non-digit non è Integer", StringHandler.isInteger("a"));
	}
	
	@Test
	public void test_MCDC_T8() {
		assertFalse("String con length>1 contenente leading-zero non va bene", StringHandler.isInteger("0.1"));
	}
}
