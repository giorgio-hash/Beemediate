package com.beemediate.beemediate.domain.utils;

import org.junit.Test;
import static org.junit.Assert.*;


public class StringHandlerIsDateTimeTest {
	
	
	//branch+statement coverage
	
	
    @Test
    public void t1_null_returnsFalse() {

        assertFalse(StringHandler.isDateTime(null));
    }

    @Test
    public void t2_wrongLength_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2020-01-01T00:00:0"));
    }

    @Test
    public void t3_badSeparatorAt4_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2020/01-01T00:00:00"));
    }
    
    @Test
    public void t4_badSeparatorAt7_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2020-01/01T00:00:00"));
    }

    @Test
    public void t5_badMainSeparatorAt10_returnsFalse() {
    	
        assertFalse(StringHandler.isDateTime("2020-01-01 00:00:00"));
    }
    
    @Test
    public void t6_badMainSeparatorAt13_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2020-01-01T00 00:00"));
    }
    
    @Test
    public void t7_badMainSeparatorAt16_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2020-01-01T00:00 00"));
    }

    @Test
    public void t8a_yearStartsZero_returnsFalse() {

        assertFalse(StringHandler.isDateTime("0200-01-01T00:00:00"));
    }
    
    @Test
    public void t8b_yearNonLeadingZero_hasNonDigitChar() {

        assertFalse(StringHandler.isDateTime("2a00-01-01T00:00:00"));
        assertFalse(StringHandler.isDateTime("20a0-01-01T00:00:00"));
        assertFalse(StringHandler.isDateTime("200a-01-01T00:00:00"));
    }

    @Test
    public void t9_validStandard_returnsTrue() {

        assertTrue(StringHandler.isDateTime("2021-01-01T00:00:00"));
    }

    @Test
    public void t10_monthZero_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2021-00-01T00:00:00"));
    }

    @Test
    public void t11_dayTooLarge_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2021-12-32T00:00:00"));
    }

    @Test
    public void t12_hourTooLarge_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2021-12-31T24:00:00"));
    }

    @Test
    public void t13_minuteTooLarge_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2021-12-31T23:60:00"));
    }

    @Test
    public void t14_secondTooLarge_returnsFalse() {

        assertFalse(StringHandler.isDateTime("2021-12-31T23:59:60"));
    }

    @Test
    public void t15_anotherValidNearEndOfMonth_returnsTrue() {
        assertTrue(StringHandler.isDateTime("2021-02-28T23:59:59"));
    }
}