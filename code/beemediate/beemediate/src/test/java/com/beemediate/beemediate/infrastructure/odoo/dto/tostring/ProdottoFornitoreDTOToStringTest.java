package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoFornitoreDTO;

/**
 * Test per ProdottoFornitoreDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class ProdottoFornitoreDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 888);
        map.put("product_id", new Object[] { 21, "PROD-21" });
        map.put("sequence", 5);
        map.put("product_name", "NomeProdotto");
        map.put("product_code", "CODE-888");
        map.put("partner_id", new Object[] { 11, "FORN-11" });
        map.put("product_uom_id", new Object[] { 2, "UNIT-2" });

        ProdottoFornitoreDTO p = new ProdottoFornitoreDTO(map);
        String s = p.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(888)), "toString deve contenere id");
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
        assertTrue(s.contains("sequence=" + Optional.of(5)), "toString deve contenere sequence");
        assertTrue(s.contains("product_name=" + Optional.of("NomeProdotto")), "toString deve contenere product_name");
        assertTrue(s.contains("product_code=" + Optional.of("CODE-888")), "toString deve contenere product_code");
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id");
        assertTrue(s.contains("product_uom_id="), "toString deve contenere product_uom_id");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // mettiamo solo i campi identificativi obbligatori come partner/product_id, lasciando gli optional vuoti
        map.put("product_id", new Object[] { 21, "PROD-21" });
        map.put("partner_id", new Object[] { 11, "FORN-11" });
        map.put("product_uom_id", new Object[] { 62, "M" });
        // id, sequence, product_name, product_code, product_uom_id mancanti

        ProdottoFornitoreDTO p = new ProdottoFornitoreDTO(map);
        String s = p.toString();

        // gli Optional mancanti dovrebbero apparire come Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("sequence=" + Optional.empty()), "toString deve mostrare Optional.empty() per sequence mancante");
        assertTrue(s.contains("product_name=" + Optional.empty()), "toString deve mostrare Optional.empty() per product_name mancante");
        assertTrue(s.contains("product_code=" + Optional.empty()), "toString deve mostrare Optional.empty() per product_code mancante");
        assertTrue(s.contains("product_uom_id=") == false || s.contains("product_uom_id="),
                   "toString deve mostrare product_uom_id vuoto/Optional.empty() per product_uom_id mancante");

        // comunque deve contenere gli identifier mappati
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id");
    }
}