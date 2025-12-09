package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;
import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.ConsegnaDTO;

/**
 * Test per ConsegnaDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class ConDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 333);
        map.put("warehouse_id", new Object[] { 10, "WH-10" });

        ConsegnaDTO c = new ConsegnaDTO(map);
        String s = c.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(333)), "toString deve contenere id");
        assertTrue(s.contains("warehouse_id="), "toString deve contenere warehouse_id");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        map.put("warehouse_id", new Object[] { 10, "WH-10" });

        ConsegnaDTO c = new ConsegnaDTO(map);
        String s = c.toString();

        // id è Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");

        // comunque deve contenere l'identifier mappato
        assertTrue(s.contains("warehouse_id="), "toString deve contenere warehouse_id anche se id optional è vuoto");
    }

}