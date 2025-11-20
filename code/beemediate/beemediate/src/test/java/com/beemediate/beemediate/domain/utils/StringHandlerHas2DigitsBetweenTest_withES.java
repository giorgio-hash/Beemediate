package com.beemediate.beemediate.domain.utils;

import org.junit.Test;
import static org.junit.Assert.*;

public class StringHandlerHas2DigitsBetweenTest {



    public void testA_nullString() {
        assertFalse(StringHandler.has2DigitsBetween(null, 0, '0', '9', '0', '9'));
    }



    public void testB_indexTooLarge() {
        String s = "12"; 
        assertFalse(StringHandler.has2DigitsBetween(s, 1, '0', '9', '0', '9')); 
    }



    public void testC_indexNegative() {
        String s = "12";
        assertFalse(StringHandler.has2DigitsBetween(s, -1, '0', '9', '0', '9'));
    }



    public void testD_startRangeFirstNonDigit() {
        String s = "12";
        assertFalse(StringHandler.has2DigitsBetween(s, 0, 'A', '9', '0', '9'));
    }



    public void testD_endRangeFirstNonDigit() {
        String s = "12";
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', 'A', '0', '9'));
    }



    public void testD_startRangeSecondNonDigit() {
        String s = "12";
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', '9', 'A', '9'));
    }



    public void testD_endRangeSecondNonDigit() {
        String s = "12";
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', '9', '0', 'A'));
    }



    public void testE_c1BelowFirstRange() {
        String s = "12"; 
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '2', '9', '0', '9'));
    }



    public void testF_c1AboveFirstRange() {
        String s = "92"; 
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', '8', '0', '9')); 
    }



    public void testH_c2BelowSecondRange() {
        String s = "10"; 
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', '9', '1', '9'));
    }



    public void testI_c2AboveSecondRange() {
        String s = "19"; 
        assertFalse(StringHandler.has2DigitsBetween(s, 0, '0', '9', '0', '8'));
    }



    public void testG_bothDigitsInRange_positiveCase() {
        String s = "12"; 
        assertTrue(StringHandler.has2DigitsBetween(s, 0, '0', '2', '0', '5'));
    }



    public void testExtra_middleIndex() {
        String s = "a123b";

        assertTrue(StringHandler.has2DigitsBetween(s, 1, '0', '2', '0', '9'));
    }
}