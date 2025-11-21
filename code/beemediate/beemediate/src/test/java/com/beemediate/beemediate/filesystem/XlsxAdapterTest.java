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

@RunWith(Parameterized.class)
public class XlsxAdapterTest {

    private final String resourcePath;
    private final String[] expectedOutput;
    
    private XlsxAdapter xlsxAdapter;

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
            
            // CASO 4: Missing Line
            // Il ciclo for di extractArticleNumbers trova una riga vuota e lancia internamente IllegalArgumentException
            // Il catch restituisce new String[0].
            { "classpath:data/sample5.xlsx", new String[] {} }
        });
    }
    

    public XlsxAdapterTest(String resourcePath, String[] expectedOutput) {
        this.resourcePath = resourcePath;
        this.expectedOutput = expectedOutput;
    }
    
    @Before
    public void setUp() {
        // Usiamo il DefaultResourceLoader reale per caricare i file da src/test/resources
        this.xlsxAdapter = new XlsxAdapter(new DefaultResourceLoader(), resourcePath);
    }
    
    @Test
    public void testReadArticleNumbers() {
    	
    	
        String[] result = xlsxAdapter.readArticleNumbers();

        assertThat(result)
            .as("Verifica lettura corretta per il file %s", resourcePath)
            .containsExactly(expectedOutput);
    }
}