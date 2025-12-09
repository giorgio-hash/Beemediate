package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.DestinazioneDTO;

/**
 * Test per DestinazioneDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class DestinazioneDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 444);
        map.put("ref", "DEST-444");

        DestinazioneDTO d = new DestinazioneDTO(map);
        String s = d.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(444)), "toString deve contenere id");
        assertTrue(s.contains("codiceDestinazione=" + Optional.of("DEST-444")), "toString deve contenere codiceDestinazione");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        // ref (codiceDestinazione) mancante

        DestinazioneDTO d = new DestinazioneDTO(map);
        String s = d.toString();

        // id e codiceDestinazione sono Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("codiceDestinazione=" + Optional.empty()), "toString deve mostrare Optional.empty() per codiceDestinazione mancante");
    }
}