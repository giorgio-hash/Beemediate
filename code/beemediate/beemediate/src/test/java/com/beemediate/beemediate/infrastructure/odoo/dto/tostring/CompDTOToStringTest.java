package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.CompagniaDTO;

/**
 * Test per CompagniaDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class CompDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 777);
        // CompagniaDTO mappa "ref" in companyRegistry (toString usa company_registry)
        map.put("ref", "REG-777");

        CompagniaDTO c = new CompagniaDTO(map);
        String s = c.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(777)), "toString deve contenere id");
        assertTrue(s.contains("company_registry=" + Optional.of("REG-777")), "toString deve contenere company_registry");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        // ref (companyRegistry) mancante

        CompagniaDTO c = new CompagniaDTO(map);
        String s = c.toString();

        // id e company_registry sono Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("company_registry=" + Optional.empty()), "toString deve mostrare Optional.empty() per company_registry mancante");
    }
}