package com.beemediate.beemediate.domain.utils;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.fail;

import org.junit.Test;

/**
 * Test fatti con Randoop che coprono
 * -	isSubstrLessOrEqualThanSubstr2
 * -	substrCompare
 * -	containsChar
 */
public class StringHandlerRandoopTest {

    public static boolean debug = false;

    @Test
    public void test1() throws Throwable {
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 10, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test2() throws Throwable {
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", (-1), 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test3() throws Throwable {
        int var4 = StringHandler.substrCompare("", "", 1, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0, var4);
    }

    @Test
    public void test4() throws Throwable {
        boolean var2 = StringHandler.containsChar("", '4');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test5() throws Throwable {
        int var4 = StringHandler.substrCompare("hi!", "", 10, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0, var4);
    }

    @Test
    public void test6() throws Throwable {
        int var4 = StringHandler.substrCompare("hi!", "hi!", 0, 1);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0, var4);
    }

    @Test
    public void test7() throws Throwable {
        boolean var2 = StringHandler.containsChar("hi!", 'a');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test8() throws Throwable {
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 10, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test9() throws Throwable {
        boolean var2 = StringHandler.containsChar("", ' ');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test10() throws Throwable {
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", (-1), 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test11() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test11");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", (-1), 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test12() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test12");
        boolean var2 = StringHandler.containsChar("", '#');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test13() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test13");
        boolean var2 = StringHandler.containsChar("hi!", '#');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test14() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test14");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 0, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test15() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test15");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", 100, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test16() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test16");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 1, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test17() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test17");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 0, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test18() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test18");
        int var4 = StringHandler.substrCompare("hi!", "hi!", (-1), (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test19() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test19");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 10, 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test20() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test20");
        boolean var2 = StringHandler.containsChar("hi!", ' ');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test21() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test21");
        boolean var2 = StringHandler.containsChar("", 'a');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test22() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test22");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", (-1), 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test23() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test23");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", (-1), 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test24() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test24");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 100, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test25() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test25");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", (-1), 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test26() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test26");
        int var4 = StringHandler.substrCompare("hi!", "hi!", 1, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(var4, 0);
    }

    @Test
    public void test27() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test27");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 100, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test28() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test28");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", (-1), (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test29() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test29");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 100, 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test30() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test30");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 0, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test31() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test31");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 10, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test32() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test32");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 100, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test33() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test33");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test34() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test34");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "hi!", 100, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test35() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test35");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 1, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test36() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test36");
        boolean var2 = StringHandler.containsChar("hi!", '4');
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var2);
    }

    @Test
    public void test37() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test37");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 0, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4 );
    }

    @Test
    public void test38() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test38");
        int var4 = StringHandler.substrCompare("hi!", "hi!", 0, 0);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(var4,0);
    }

    @Test
    public void test39() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test39");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 100, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test40() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test40");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 0, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test41() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test41");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", 1, 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test42() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test42");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 0, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test43() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test43");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 10, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test44() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test44");
        int var4 = StringHandler.substrCompare("hi!", "", 0, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(var4, 0);
    }

    @Test
    public void test45() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test45");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 1, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test46() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test46");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 1, 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test47() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test47");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", (-1), 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test48() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test48");
        int var4 = StringHandler.substrCompare("hi!", "hi!", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test49() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test49");
        int var4 = StringHandler.substrCompare("hi!", "hi!", (-1), 0);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test50() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test50");
        int var4 = StringHandler.substrCompare("", "", (-1), (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test51() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test51");
        int var4 = StringHandler.substrCompare("", "hi!", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test52() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test52");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "hi!", 1, 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test53() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test53");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", (-1), 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test54() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test54");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 0, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test55() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test55");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "hi!", 10, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test56() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test56");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test57() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test57");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 0, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test58() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test58");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", (-1), 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test59() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test59");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", (-1), (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test60() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test60");
        int var4 = StringHandler.substrCompare("", "", 0, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test61() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test61");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 100, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test62() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test62");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 10, 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test63() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test63");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "", 0, 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test64() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test64");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 0, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test65() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test65");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", 1, 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test66() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test66");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 100, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test67() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test67");
        int var4 = StringHandler.substrCompare("hi!", "", (-1), 0);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test68() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test68");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "", (-1), 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test69() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test69");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 10, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test70() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test70");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 100, 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test71() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test71");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 10, 100);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test72() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test72");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", (-1), 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test73() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test73");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 1, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test74() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test74");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 10, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test75() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test75");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", (-1), 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test76() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test76");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "", (-1), 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test77() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test77");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 1, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test78() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test78");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 0, 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test79() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test79");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 100, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test80() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test80");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", 10, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test81() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test81");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", (-1), (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test82() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test82");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 0, 1);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test83() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test83");
        int var4 = StringHandler.substrCompare("", "hi!", 10, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test84() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test84");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", 0, 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test85() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test85");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 100, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test86() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test86");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "hi!", 0, 1);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test87() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test87");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "", (-1), 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test88() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test88");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("", "", (-1), 10);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

    @Test
    public void test89() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test89");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test90() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test90");
        int var4 = StringHandler.substrCompare("", "", 100, 0);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(var4 , 0);
    }

    @Test
    public void test91() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test91");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "", 0, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test92() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test92");
        int var4 = StringHandler.substrCompare("", "hi!", 10, 0);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test93() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test93");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 10, 0);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test94() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test94");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "", (-1), 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test95() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test95");
        int var4 = StringHandler.substrCompare("", "", 100, (-1));
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test96() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test96");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("", "hi!", 100, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test97() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test97");
        int var4 = StringHandler.substrCompare("hi!", "hi!", 1, 1);
        // Regression assertion (captures the current behavior of the code)
        assertEquals(0,var4);
    }

    @Test
    public void test98() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test98");
        boolean var4 = StringHandler.isSubstr1LessOrEqualThanSubstr2("hi!", "hi!", 1, 10);
        // Regression assertion (captures the current behavior of the code)
        assertFalse(var4);
    }

    @Test
    public void test99() throws Throwable {
        if (debug) System.out.printf("%nRandoopTest0.test99");
        // The following exception was thrown during execution.
        // This behavior will recorded for regression testing.
        try {
            int var4 = StringHandler.substrCompare("hi!", "hi!", 0, 100);
            fail("Expected exception of type java.lang.StringIndexOutOfBoundsException");
        } catch (java.lang.StringIndexOutOfBoundsException e) {
            // Expected exception.
        }
    }

}