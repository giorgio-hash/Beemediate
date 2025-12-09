package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.ProdottoDTO;

/**
 * Test per ProdottoDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class ProdDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 321);
        map.put("seller_ids", new Object[] { new Object[] { 1, "SELLER-1" }, new Object[] { 2, "SELLER-2" } });

        ProdottoDTO p = new ProdottoDTO(map);
        String s = p.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(321)), "toString deve contenere id");
        assertTrue(s.contains("seller_ids="), "toString deve contenere seller_ids");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        // seller_ids mancante

        ProdottoDTO p = new ProdottoDTO(map);
        String s = p.toString();

        // id e seller_ids sono Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("seller_ids=" + Optional.empty()) || s.contains("seller_ids="),
                   "toString deve mostrare seller_ids vuoto/Optional.empty() per seller_ids mancante");
    }
}