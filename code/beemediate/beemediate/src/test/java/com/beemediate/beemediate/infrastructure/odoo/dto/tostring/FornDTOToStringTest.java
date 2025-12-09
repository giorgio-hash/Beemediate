package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.FornitoreDTO;

/**
 * Test per FornitoreDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class FornDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 777);
        map.put("name", "GEALAN");
        map.put("ref", "AZ-777");

        FornitoreDTO f = new FornitoreDTO(map);
        String s = f.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("name=" + Optional.of("GEALAN")), "toString deve contenere name");
        assertTrue(s.contains("codiceAzienda=" + Optional.of("AZ-777")), "toString deve contenere codiceAzienda");
        assertTrue(s.contains("id=" + Optional.of(777)), "toString deve contenere id");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // name mancante
        // ref mancante
        // id mancante

        FornitoreDTO f = new FornitoreDTO(map);
        String s = f.toString();

        // tutti i campi opzionali dovrebbero apparire come Optional.empty()
        assertTrue(s.contains("name=" + Optional.empty()), "toString deve mostrare Optional.empty() per name mancante");
        assertTrue(s.contains("codiceAzienda=" + Optional.empty()), "toString deve mostrare Optional.empty() per codiceAzienda mancante");
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
    }
}