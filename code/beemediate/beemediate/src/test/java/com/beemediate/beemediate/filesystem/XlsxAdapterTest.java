package com.beemediate.beemediate.filesystem;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.springframework.core.io.DefaultResourceLoader;

import com.beemediate.beemediate.infrastructure.filesystem.XlsxAdapter;

/**
 * Test parametrizzato per XlsxAdapter che verifica lettura di codici articolo
 * da diversi file di risorse (happy path, file vuoti, formati non validi).
 */
@RunWith(Parameterized.class)
public class XlsxAdapterTest {

    /** Percorso della risorsa da caricare per il test (es. classpath:...). */
    private final String resourcePath;
    /** Valori attesi dei codici articolo letti dal file di test. */
    private final String[] expectedOutput;
    /** Istanza di XlsxAdapter utilizzata per l'accesso ai file di test. */
    private XlsxAdapter xlsxAdapter;

    /**
     * Parametri per i test parametrizzati di XlsxAdapter.
     *
     * Ogni entry è una coppia {percorso risorsa, valori attesi} che rappresenta uno scenario di test:
     * - sample1.xlsx: file valido con dati — restituisce i valori esatti {"210100","210102"}.
     * - sample2.xlsx: solo intestazione — nessuna riga di dati, restituisce array vuoto.
     * - sample3.xlsx: file vuoto / senza header — XlsxAdapter solleva IllegalArgumentException internamente; il test si aspetta array vuoto.
     * - sample4.txt: formato non valido (ad es. file di testo) — XSSFWorkbook lancia IOException; il test si aspetta array vuoto.
     * - sample5.xlsx: riga mancante/irregolare — extractArticleNumbers solleva IllegalArgumentException internamente; il test si aspetta array vuoto.
     *
     * @return Collection di Object[] dove ogni Object[] contiene {String resourcePath, String[] expectedArticleNumbers}
     */
    @Parameters(name = "{index}: File={0}")
    public static Collection<Object[]> parameters() {
        return Arrays.asList(new Object[][]{
            // CASO 1: Happy Path
            // Il file esiste e ha dati. Ci aspettiamo i valori esatti.
            { "classpath:data/sample1.xlsx", new String[] {"210100", "210102"} }, 

            // CASO 2: Header Only
            // Il file ha solo l'intestazione. Il loop non parte. Ritorna array vuoto.
            { "classpath:data/sample2.xlsx", new String[] {} },

            // CASO 3: Empty File / No Header
            // XlsxAdapter lancia internamente IllegalArgumentException.
            // Il catch restituisce new String[0].
            { "classpath:data/sample3.xlsx", new String[] {} },

            // CASO 4: Invalid Format (es. file di testo)
            // XSSFWorkbook lancia IOException.
            // Il catch restituisce new String[0].
            { "classpath:data/sample4.txt", new String[] {} },
            
            // CASO 5: Missing Line
            // Il ciclo for di extractArticleNumbers trova una riga vuota e lancia internamente IllegalArgumentException
            // Il catch restituisce new String[0].
            { "classpath:data/sample5.xlsx", new String[] {} }
        });
    }
    

    /**
     * Crea un'istanza di test per l'adattatore XLSX.
     *
     * @param resourcePath percorso della risorsa di test (.xlsx) da caricare
     * @param expectedOutput array di stringhe contenente l'output atteso dal test
     */
    public XlsxAdapterTest(String resourcePath, String[] expectedOutput) {
        this.resourcePath = resourcePath;
        this.expectedOutput = expectedOutput;
    }
    
    /**
     * Inizializza l'XlsxAdapter prima di ogni test.
     * Utilizza un DefaultResourceLoader reale per caricare i file da src/test/resources
     * e passa il resourcePath configurato all'adapter.
     */
    @Before
    public void setUp() {
        // Usiamo il DefaultResourceLoader reale per caricare i file da src/test/resources
        this.xlsxAdapter = new XlsxAdapter(new DefaultResourceLoader(), resourcePath);
    }
    
    /**
     * Test JUnit per il metodo XlsxAdapter.readArticleNumbers().
     *
     * Verifica che l'adapter legga correttamente i numeri articolo dal file di risorse
     * specificato (resourcePath) e che l'array ritornato sia esattamente uguale
     * a expectedOutput (stesso ordine e stesso contenuto).
     *
     * Precondizioni:
     * - L'istanza xlsxAdapter è correttamente inizializzata.
     * - La risorsa identificata da resourcePath esiste ed è nel formato previsto (foglio Excel
     *   contenente i numeri articolo).
     *
     * Comportamento atteso:
     * - Chiamando xlsxAdapter.readArticleNumbers() viene restituito un array di stringhe
     *   che corrisponde esattamente a expectedOutput.
     * - In caso di discrepanza, l'asserzione produce un messaggio che include resourcePath
     *   per semplificare il debug.
     *
     * Note:
     * - Eventuali eccezioni durante la lettura del file provocano il fallimento del test.
     *
     * @see com.beemediate.beemediate.filesystem.XlsxAdapter#readArticleNumbers()
     */
    @Test
    public void testReadArticleNumbers() {
    	
    	
        String[] result = xlsxAdapter.readArticleNumbers();

        assertThat(result)
            .as("Verifica lettura corretta per il file %s", resourcePath)
            .containsExactly(expectedOutput);
    }
}