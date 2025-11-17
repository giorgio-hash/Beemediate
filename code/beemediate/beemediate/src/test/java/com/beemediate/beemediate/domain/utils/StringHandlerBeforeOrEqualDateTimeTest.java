package com.beemediate.beemediate.domain.utils;

import org.junit.Test;
import static org.junit.Assert.*;

public class StringHandlerBeforeOrEqualDateTimeTest {


    @Test
    public void test_date1Null_date2Valid() {
        String date1 = null;
        String date2 = "2020-01-01T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_date1Valid_date2Null() {
        String date1 = "2020-01-01T00:00:00";
        String date2 = null;
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_equalDatetimes() {
        String date1 = "2020-01-01T00:00:00";
        String date2 = "2020-01-01T00:00:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_yearLess_than() {
        String date1 = "2020-01-01T00:00:00";
        String date2 = "2021-01-01T00:00:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_yearGreater_than() {
        String date1 = "2022-01-01T00:00:00";
        String date2 = "2021-01-01T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_monthLess_than() {
        String date1 = "2021-02-01T00:00:00";
        String date2 = "2021-03-01T00:00:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_monthGreater_than() {
        String date1 = "2021-04-01T00:00:00";
        String date2 = "2021-03-01T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_dayLess_than() {
        String date1 = "2021-03-05T00:00:00";
        String date2 = "2021-03-06T00:00:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_dayGreater_than() {
        String date1 = "2021-03-07T00:00:00";
        String date2 = "2021-03-06T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_hourLess_than() {
        String date1 = "2021-03-06T08:00:00";
        String date2 = "2021-03-06T09:00:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_hourGreater_than() {
        String date1 = "2021-03-06T10:00:00";
        String date2 = "2021-03-06T09:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_minuteLess_than() {
        String date1 = "2021-03-06T09:10:00";
        String date2 = "2021-03-06T09:11:00";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_minuteGreater_than() {
        String date1 = "2021-03-06T09:12:00";
        String date2 = "2021-03-06T09:11:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_secondLess_than() {
        String date1 = "2021-03-06T09:11:20";
        String date2 = "2021-03-06T09:11:21";
        assertTrue(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_secondGreater_than() {
        String date1 = "2021-03-06T09:11:22";
        String date2 = "2021-03-06T09:11:21";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }


    @Test
    public void test_invalidFormat_space_not_T() {
        String date1 = "2021-03-06 09:11:21"; // spazio al posto di 'T'
        String date2 = "2021-03-06T09:11:21";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }
}