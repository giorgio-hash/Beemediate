package com.beemediate.beemediate.infrastructure.odoo.config;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * Test parametrico per verificare la consistenza delle etichette (label) dell'enum {@link OafStatus}.
 * <p>
 * Utilizza il runner {@link Parameterized} di JUnit 4 per eseguire lo stesso test di confronto
 * su tutte le costanti definite nell'enumerazione, garantendo che ogni stato abbia la rappresentazione
 * a stringa attesa.
 */
@RunWith(Parameterized.class)
public class OaFStatusParamTest {
	
    /** L'istanza dell'enum sotto test. */
    private final OafStatus status;
    /** Il valore della label atteso per l'istanza corrente. */
    private final String expectedLabel;

/**
     * Fornisce i dati per l'esecuzione del test parametrico.
     * * @return Una collezione di array di oggetti, dove ogni array contiene:
     * <ol>
     * <li>L'istanza di {@link OafStatus} da testare.</li>
     * <li>La stringa (label) attesa corrispondente.</li>
     * </ol>
     */
    @Parameters
    public static Collection<Object[]> parameters() {
        return Arrays.asList(
                new Object []{ OafStatus.NEW, "NEW" },
                new Object []{ OafStatus.SHIPPED, "SHIPPED" },
                new Object []{ OafStatus.CONFIRMED, "CONFIRMED" },
                new Object []{ OafStatus.OPENTRANSERROR, "OPENTRANSERROR" },
                new Object []{ OafStatus.CONTENTERROR, "CONTENTERROR" }
        );
    }

/**
     * Costruttore utilizzato dal runner per iniettare i parametri del singolo caso di test.
     *
     * @param status l'enum da verificare.
     * @param expectedLabel la label che l'enum dovrebbe possedere.
     */
    public OaFStatusParamTest(OafStatus status, String expectedLabel) {
        this.status = status;
        this.expectedLabel = expectedLabel;
    }

/**
     * Verifica che la proprietà {@code label} dell'enum corrisponda esattamente alla stringa attesa.
     */
    @Test
    public void labelMatchesExpected() {
        assertEquals(expectedLabel, status.label);
    }
}