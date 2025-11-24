package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.IdentifierDTO;

/**
 * Test per IdentifierDTO.toString()
 * Stesso stile e approccio dei test per ArticoloPreventivoDTO.toString()
 */
public class IdentifierDTOToStringTest {

    @Test
    void toString_includesAllFields_whenAllPresent() {
        Object[] array = new Object[] { 123, "NAME-123" };

        IdentifierDTO id = new IdentifierDTO(array);
        String s = id.toString();

        // verifica che la stringa contenga i valori principali (Optional.of)
        assertTrue(s.contains("num=" + Optional.of(123)), "toString deve contenere num");
        assertTrue(s.contains("name=" + Optional.of("NAME-123")), "toString deve contenere name");
    }

    @Test
    void toString_handlesMissingOptionalsGracefully() {
        // passiamo valori null per simulare campi mancanti -> AttributeMapper dovrebbe produrre Optional.empty()
        Object[] array = new Object[] { null, null };

        IdentifierDTO id = new IdentifierDTO(array);
        String s = id.toString();

        // num e name dovrebbero essere Optional.empty()
        assertTrue(s.contains("num=" + Optional.empty()), "toString deve mostrare Optional.empty() per num mancante");
        assertTrue(s.contains("name=" + Optional.empty()), "toString deve mostrare Optional.empty() per name mancante");
    }
}