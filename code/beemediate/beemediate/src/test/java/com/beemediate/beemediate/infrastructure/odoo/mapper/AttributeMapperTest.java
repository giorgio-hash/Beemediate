package com.beemediate.beemediate.infrastructure.odoo.mapper;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Optional;

import org.junit.Test;


public class AttributeMapperTest {

	// --- stringify tests ---
    @Test
    public void stringify_returnsOptionalForString() {
        Optional<String> res = AttributeMapper.stringify("hello");
        assertTrue(res.isPresent());
        assertEquals("hello", res.get());
    }

    @Test
    public void stringify_returnsEmptyForNonString() {
        Optional<String> res = AttributeMapper.stringify(123);
        assertFalse(res.isPresent());
    }

    @Test
    public void stringify_returnsEmptyForNull() {
        Optional<String> res = AttributeMapper.stringify(null);
        assertFalse(res.isPresent());
    }

    // --- intify tests ---
    @Test
    public void intify_returnsOptionalForInteger() {
        Optional<Integer> res = AttributeMapper.intify(10);
        assertTrue(res.isPresent());
        assertEquals(10, res.get().intValue());
    }

    @Test
    public void intify_returnsEmptyForNonInteger() {
        Optional<Integer> res = AttributeMapper.intify("10");
        assertFalse(res.isPresent());
    }

    @Test
    public void intify_returnsEmptyForNull() {
        Optional<Integer> res = AttributeMapper.intify(null);
        assertFalse(res.isPresent());
    }

    // --- toArray tests ---
    @Test
    public void toArray_returnsOptionalForArray() {
        Object[] arr = new Object[] { "a", 1, true };
        Optional<Object[]> res = AttributeMapper.toArray(arr);
        assertTrue(res.isPresent());
        assertSame(arr, res.get());
        assertEquals(3, res.get().length);
    }

    @Test
    public void toArray_returnsEmptyForNonArray() {
        Optional<Object[]> res = AttributeMapper.toArray("not an array");
        assertFalse(res.isPresent());
    }

    @Test
    public void toArray_returnsEmptyForNull() {
        Optional<Object[]> res = AttributeMapper.toArray(null);
        assertFalse(res.isPresent());
    }

    // --- booleanify tests ---
    @Test
    public void booleanify_returnsOptionalForTrue() {
        Optional<Boolean> res = AttributeMapper.booleanify(Boolean.TRUE);
        assertTrue(res.isPresent());
        assertTrue(res.get());
    }

    @Test
    public void booleanify_returnsOptionalForFalse() {
        Optional<Boolean> res = AttributeMapper.booleanify(Boolean.FALSE);
        assertTrue(res.isPresent());
        assertFalse(res.get());
    }

    @Test
    public void booleanify_returnsEmptyForNonBoolean() {
        Optional<Boolean> res = AttributeMapper.booleanify("true");
        assertFalse(res.isPresent());
    }

    @Test
    public void booleanify_returnsEmptyForNull() {
        Optional<Boolean> res = AttributeMapper.booleanify(null);
        assertFalse(res.isPresent());
    }

    // --- doublify tests ---
    @Test
    public void doublify_returnsOptionalForDouble() {
        Optional<Double> res = AttributeMapper.doublify(12.34d);
        assertTrue(res.isPresent());
        assertEquals(12.34d, res.get(), 0.0d);
    }

    @Test
    public void doublify_returnsOptionalForNonDoubleNumber() {
        Optional<Double> res = AttributeMapper.doublify(Integer.valueOf(5));
        assertTrue(res.isPresent());
        assertEquals(5.0d, res.get(), 0.0d);
        Optional<Double> resFloat = AttributeMapper.doublify(Float.valueOf(2.5f));
        Optional<Double> resLong = AttributeMapper.doublify(Long.valueOf(3L));
        assertTrue(resFloat.isPresent());
        assertEquals(2.5d, resFloat.get(), 0.0d);
        assertTrue(resLong.isPresent());
        assertEquals(3.0d, resLong.get(), 0.0d);
    }

    @Test
    public void doublify_returnsEmptyForNonNumber() {
        Optional<Double> res = AttributeMapper.doublify("12.3");
        assertFalse(res.isPresent());
    }

    @Test
    public void doublify_returnsEmptyForNull() {
        Optional<Double> res = AttributeMapper.doublify(null);
        assertFalse(res.isPresent());
    }

    // --- toLocalDateTime tests (MCDC oriented) ---
    @Test
    public void toLocalDateTime_parsesValidString() {
    	DateTimeFormatter fmt = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        LocalDateTime expected = LocalDateTime.of(2020, 12, 31, 23, 59, 59);
        String s = expected.format(fmt);
        Optional<LocalDateTime> res = AttributeMapper.toLocalDateTime(s);
        assertTrue(res.isPresent());
        assertEquals(expected, res.get());
    }

    @Test
    public void toLocalDateTime_returnsEmptyForMalformedString() {
        String bad = "2020-12-31T23:59"; // wrong format
        Optional<LocalDateTime> res = AttributeMapper.toLocalDateTime(bad);
        assertFalse(res.isPresent());
    }

    @Test
    public void toLocalDateTime_returnsEmptyForNonString() {
        Optional<LocalDateTime> res = AttributeMapper.toLocalDateTime(12345);
        assertFalse(res.isPresent());
    }

    @Test
    public void toLocalDateTime_returnsEmptyForNull() {
        Optional<LocalDateTime> res = AttributeMapper.toLocalDateTime(null);
        assertFalse(res.isPresent());
    }

    @Test
    public void toLocalDateTime_returnsEmptyForNonsensicalDate() {
        String bad = "2020-13-01 00:00:00"; // month 13 invalid
        Optional<LocalDateTime> res = AttributeMapper.toLocalDateTime(bad);
        assertFalse(res.isPresent());
    }
}