package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 * Test generati con EvoSuite per isDigit e has2DigitsBetween
 */
public class Has2DigitsBtwn_WithES {
	
	

	  @Test(timeout = 4000)
	  public void test00()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('9', true);
	      assertTrue(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test01()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('1', true);
	      assertTrue(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test02()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("cbN4M", 3, '4', '4', '6', '4');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test03()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("00", 0, '0', '0', '0', '4');
	      assertTrue(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test04()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("0N", 0, '0', '1', '0', '1');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test05()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("bN", 0, '4', '4', '8', '8');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test06()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("G", 0, ')', 'I', '|', 'N');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test07()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('H', false);
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test08()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('3', false);
	      assertTrue(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test09()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('-', false);
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test10()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('.', true);
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test11()  throws Throwable  {
	      boolean boolean0 = StringHandler.isDigit('b', true);
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test12()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("cbN4#", 3, '4', '4', '4', '4');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test13()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("bN", 0, '9', '9', '9', '9');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test14()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("cbN(M", 3, '4', '4', '4', '4');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test15()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("ogDIzSI", 0, '9', '9', '9', 'k');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test16()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("bN", 0, '9', '9', 'S', 'S');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test17()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("00", 0, '0', '0', '0', '0');
	      assertTrue(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test18()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("lJ", 0, 'o', '3', '.', '3');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test19()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("Lf", 0, '4', 'b', '4', 'b');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test20()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("", (-1), '0', '0', '0', '0');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test21()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween((String) null, '3', '3', '3', '3', '3');
	      assertFalse(boolean0);
	  }

	  @Test(timeout = 4000)
	  public void test22()  throws Throwable  {
	      boolean boolean0 = StringHandler.has2DigitsBetween("", 0, '4', 'b', '4', 'b');
	      assertFalse(boolean0);
	  }

	}
