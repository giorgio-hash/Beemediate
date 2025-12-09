package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.ContattoConsegnaDTO;

/**
 * Test per ContattoConsegnaDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class ConConDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 101);
        map.put("partner_id", new Object[] { 30, "PARTNER-30" });

        ContattoConsegnaDTO c = new ContattoConsegnaDTO(map);
        String s = c.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(101)), "toString deve contenere id");
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        map.put("partner_id", new Object[] { 30, "PARTNER-30" });

        ContattoConsegnaDTO c = new ContattoConsegnaDTO(map);
        String s = c.toString();

        // id è Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");

        // comunque deve contenere l'identifier mappato
        assertTrue(s.contains("partner_id="), "toString deve contenere partner_id anche se id optional è vuoto");
    }
}