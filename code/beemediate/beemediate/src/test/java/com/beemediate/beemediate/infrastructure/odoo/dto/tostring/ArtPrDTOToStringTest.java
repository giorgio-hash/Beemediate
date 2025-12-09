package com.beemediate.beemediate.infrastructure.odoo.dto.tostring;

import static org.junit.jupiter.api.Assertions.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.junit.jupiter.api.Test;

import com.beemediate.beemediate.infrastructure.odoo.dto.ArticoloPreventivoDTO;

/**
 * Test per ArticoloPreventivoDTO.toString()
 */
public class ArtPrDTOToStringTest {

/**
     * Verifica che il metodo {@code toString} includa tutti i campi quando il DTO è interamente popolato.
     * <p>
     * Scenario:
     * <ul>
     * <li>La mappa di input contiene valori per id, order_id, product_id e product_qty.</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>La stringa risultante contiene le rappresentazioni testuali di tutti i valori inseriti.</li>
     * </ul>
     */
    @Test
    void toString_includesAllFields_whenAllPresent() {
        Map<String, Object> map = new HashMap<>();
        map.put("id", 555);
        map.put("order_id", new Object[] { 10, "PO-10" });
        map.put("product_id", new Object[] { 20, "PRODUCT-20" });
        map.put("product_qty", 12.5d);

        ArticoloPreventivoDTO a = new ArticoloPreventivoDTO(map);
        String s = a.toString();

        // verifica che la stringa contenga i valori principali
        assertTrue(s.contains("id=" + Optional.of(555)), "toString deve contenere id");
        assertTrue(s.contains("order_id="), "toString deve contenere order_id");
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
        assertTrue(s.contains("product_qty=" + Optional.of(12.5d)), "toString deve contenere product_qty");
    }

/**
     * Verifica che il metodo {@code toString} gestisca correttamente i campi opzionali mancanti.
     * <p>
     * Scenario:
     * <ul>
     * <li>La mappa di input non contiene le chiavi per "id" e "product_qty".</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>Non vengono sollevate eccezioni.</li>
     * <li>La stringa mostra esplicitamente {@code Optional.empty} per i campi mancanti.</li>
     * <li>I campi presenti (order_id, product_id) vengono comunque renderizzati correttamente.</li>
     * </ul>
     */
    @Test
    void toString_handlesMissingOptionalsGracefully() {
        Map<String, Object> map = new HashMap<>();
        // id mancante
        map.put("order_id", new Object[] { 10, "PO-10" });
        map.put("product_id", new Object[] { 20, "PRODUCT-20" });
        // product_qty mancante

        ArticoloPreventivoDTO a = new ArticoloPreventivoDTO(map);
        String s = a.toString();

        // id e product_qty sono Optional.empty()
        assertTrue(s.contains("id=" + Optional.empty()), "toString deve mostrare Optional.empty() per id mancante");
        assertTrue(s.contains("product_qty=" + Optional.empty()), "toString deve mostrare Optional.empty() per product_qty mancante");

        // comunque deve contenere gli identifier mappati
        assertTrue(s.contains("order_id="), "toString deve contenere order_id anche se id optional è vuoto");
        assertTrue(s.contains("product_id="), "toString deve contenere product_id");
    }

}