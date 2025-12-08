package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

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

	@Test
	public void test_MCDC_T0_T5_T6() {
		assertTrue("test suite per happy path (T0, T5, T6)", StringHandler.equals("matteo", "matteo"));
	}
	
	@Test
	public void test_MCDC_T1() {
		assertFalse("test suite per s1=null (T1)", StringHandler.equals(null, "matteo"));
	} 
	
	@Test
	public void test_MCDC_T2() {
		assertFalse("test suite per s1!=null, s2=null (T2)", StringHandler.equals("matteo", null));
	} 

	@Test
	public void test_MCDC_T3() {
		assertFalse("test suite per s1.length()!=s2.length() (T3)", StringHandler.equals("", "matteo"));
	}
	
	@Test
	public void test_MCDC_T4() {
		assertTrue("test suite per s1.length()==0 (T4)", StringHandler.equals("", ""));
	}
	
	@Test
	public void test_MCDC_T7() {
		assertFalse("test suite per lettera diversa (T7)", StringHandler.equals("abc", "abd"));
	}
}