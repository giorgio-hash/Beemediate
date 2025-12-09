package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.time.LocalDateTime;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.PreventivoDTO;

/**
 * Test per PreventivoDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class PrevDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 999);
        map.put("name", "PREV-999");
        map.put("partner_id", new Object[] { 11, "FORNITORE-11" });
        map.put("product_id", new Object[] { 22, "PRODUCT-22" });
        map.put("currency_id", new Object[] { 33, "EUR" });
        map.put("picking_type_id", new Object[] { 44, "DELIVERY-44" });
        map.put("company_id", new Object[] { 55, "COMPANY-55" });
        map.put("origin", "ORIG-123");
        map.put("order_line", new Object[] { 101, 102 });
        // toString prints the Optional-wrapped LocalDateTime values; use non-null values to appear in Optional.of(...)
        map.put("date_order", LocalDateTime.of(2025, 1, 2, 3, 4, 5));
        map.put("date_approve", LocalDateTime.of(2025, 1, 3, 4, 5, 6));
        map.put("date_planned", LocalDateTime.of(2025, 1, 4, 5, 6, 7));

        PreventivoDTO p = new PreventivoDTO(map);
        String s = p.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(999)), "toString deve contenere id");
        assertTrue(s.contains("name=" + Optional.of("PREV-999")), "toString deve contenere name");
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id");
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
        assertTrue(s.contains("currency_id="), "toString deve contenere currency_id");
        assertTrue(s.contains("picking_type_id="), "toString deve contenere picking_type_id");
        assertTrue(s.contains("company_id="), "toString deve contenere company_id");
        assertTrue(s.contains("origin=" + Optional.of("ORIG-123")), "toString deve contenere origin");
        assertTrue(s.contains("order_line="), "toString deve contenere order_line");
        assertTrue(s.contains("date_order="), "toString deve contenere date_order");
        assertTrue(s.contains("date_approve="), "toString deve contenere date_approve");
        assertTrue(s.contains("date_planned="), "toString deve contenere date_planned");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // Simula mancanza di molti optional: non mettiamo id, name, origin e date_*
        map.put("partner_id", new Object[] { 11, "FORNITORE-11" });
        map.put("product_id", new Object[] { 22, "PRODUCT-22" });
        map.put("currency_id", new Object[] { 33, "EUR" });
        map.put("picking_type_id", new Object[] { 44, "DELIVERY-44" });
        map.put("company_id", new Object[] { 55, "COMPANY-55" });
        map.put("order_line", null); // order_line assente

        PreventivoDTO p = new PreventivoDTO(map);
        String s = p.toString();

        // gli Optional mancanti dovrebbero apparire come Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("name=" + Optional.empty()), "toString deve mostrare Optional.empty() per name mancante");
        assertTrue(s.contains("origin=" + Optional.empty()), "toString deve mostrare Optional.empty() per origin mancante");
        assertTrue(s.contains("order_line=" + Optional.empty()) || s.contains("order_line="), "toString deve mostrare order_line vuoto/Optional.empty()");
        // comunque deve contenere gli identifier mappati
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id");
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
    }
}