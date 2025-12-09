package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * testing MCDC del metodo <i>StringHandler.equals()</i>.
 * <ul><li>Decisione 1: if (s1==null || s2==null 	||	s1.length() != s2.length())
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>s1==null</th>
 * <th>s2==null</th>
 * <th>s1.length() != s2.length()</th>
 * <th>esito cond.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T0</td> <td>F</td> <td>F</td> <td>F</td> <td>false</td> <td>(prosegue)</td> <td>s1="matteo", s2="matteo"</td>
 * </tr>
 * <tr>
 * <td>T1</td> <td>T</td> <td>-</td> <td>-</td> <td>true</td> <td>false</td> <td>s1=null, s2="matteo"</td>
 * </tr>
 * <tr>
 * <td>T2</td> <td>F</td> <td>T</td> <td>-</td> <td>true</td> <td>false</td> <td>s1="matteo", s2=null</td>
 * </tr>
 * <tr>
 * <td>T3</td> <td>F</td> <td>F</td> <td>T</td> <td>true</td> <td>false</td> <td>s1="", s2="matteo"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 2: if (s1.length() == 0)
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>s1.length() == 0</th>
 * <th>esito cond.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T4</td> <td>T</td> <td>true</td> <td>true</td> <td>s1="", s2=""</td>
 * </tr>
 * <tr>
 * <td>T5</td> <td>F</td> <td>false</td> <td>(prosegue)</td> <td>s1="matteo", s2="matteo"</td>
 * </tr>
 * </table>
 * </p></li>
 * <li>Decisione 3: if(s1.charAt(i) != s2.charAt(i))
 * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>(s1.charAt(i) != s2.charAt(i))</th>
 * <th>esito cond.</th>
 * <th>esito metodo</th>
 * <th>input</th>
 * </tr>
 * <tr>
 * <td>T6</td> <td>F</td> <td>false</td> <td>false</td> <td>s1="matteo", s2="matteo"</td>
 * </tr>
 * <tr>
 * <td>T7</td> <td>T</td> <td>true</td> <td>true</td> <td>s1="abc", s2="abd"</td>
 * </tr>
 * </table>
 * </p></li>
 * </ul>
 */
public class StringHandlerEquals {

	//if (s1==null || s2==null 	||	s1.length() != s2.length())
	/*	CASE	s1==null		s2==null		s1.length() != s2.length()	|	esito cond.	|	esito metodo	|	input
	 * 	T0			F				F				F						|	false		|	(prosegue)		|	s1="matteo",	s2="matteo"
	 * 	T1			T				-				-						|	true		|	false			|	s1=null,		s2="matteo"
	 * 	T2			F				T				-						|	true		|	false			|	s1="matteo",	s2=null
	 * 	T3			F				F				T						|	true		|	false			|	s1="",			s2="matteo"
	 * */
	
	//if (s1.length() == 0)
	/**	CASE	s1.length() == 0	|	esito cond.	|	esito metodo	|	input
	 * 	T4			T				|	true		|	true			|	s1="",			s2=""
	 * 	T5			F				|	false		|	(prosegue)		|	s1="matteo", 	s2="matteo"
	 */
	
	//if(s1.charAt(i) != s2.charAt(i))
	/** CASE	(s1.charAt(i) != s2.charAt(i))	| esito	cond.	|	esito metodo	|	input
	 * 	T6					F					| false			|	false			|	s1="matteo",	s2="matteo"
	 * 	T7					T					| true			|	true			|	s1="abc",	s2="abd"
	 */

	/**
	 * Testa i casi T0, T5, T6
	 */
	@Test
	public void test_MCDC_T0_T5_T6() {
		assertTrue("test suite per happy path (T0, T5, T6)", StringHandler.equals("matteo", "matteo"));
	}
	
		/**
	 * Testa il caso T1
	 */
	@Test
	public void test_MCDC_T1() {
		assertFalse("test suite per s1=null (T1)", StringHandler.equals(null, "matteo"));
	} 

		/**
	 * Testa il caso T2
	 */
	@Test
	public void test_MCDC_T2() {
		assertFalse("test suite per s1!=null, s2=null (T2)", StringHandler.equals("matteo", null));
	} 

			/**
	 * Testa il caso T3
	 */
	@Test
	public void test_MCDC_T3() {
		assertFalse("test suite per s1.length()!=s2.length() (T3)", StringHandler.equals("", "matteo"));
	}

				/**
	 * Testa il caso T4
	 */
	@Test
	public void test_MCDC_T4() {
		assertTrue("test suite per s1.length()==0 (T4)", StringHandler.equals("", ""));
	}
	
				/**
	 * Testa il caso T7
	 */
	@Test
	public void test_MCDC_T7() {
		assertFalse("test suite per lettera diversa (T7)", StringHandler.equals("abc", "abd"));
	}
}