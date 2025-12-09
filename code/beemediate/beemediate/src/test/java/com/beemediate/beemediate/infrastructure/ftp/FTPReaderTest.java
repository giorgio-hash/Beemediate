package com.beemediate.beemediate.infrastructure.ftp;

import static org.junit.jupiter.api.Assertions.*;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import com.beemediate.beemediate.infrastructure.ftp.config.FTPConfig;
import com.beemediate.beemediate.infrastructure.ftp.dto.confirmation.XmlOrderResponse;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;
import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;

/**
 * Test per la classe {@link FTPReader}. Usa MockedStatic per DataMapper e istanze reali di ConfirmationStructure (mock ben fatto).
 * <p>
 * Verifica la logica di scansione e lettura dei file dal filesystem locale (simulato tramite {@link TempDir}).
 * <p>
 * <b>Nota sull'architettura del test:</b><br>
 * Viene utilizzato {@link MockedStatic} di Mockito per isolare {@link FTPReader} dalla dipendenza statica
 * {@link DataMapper}. Questo permette di testare il flusso di lettura dei file senza eseguire
 * realmente il parsing XML, che è testato separatamente.
 */
public class FTPReaderTest {
	
    /** Gestito da JUnit 5: crea una directory temporanea isolata per ogni esecuzione o per la classe. */
    @TempDir
    Path tempDir;

    private Path inbound;
    private Path outbound;
    private Path archived;
    private FTPConfig cfg;
    
    /** * Mock statico per {@link DataMapper}. 
     * Deve essere statico e gestito in @BeforeAll/@AfterAll per validità nell'intero ciclo di vita dei test.
     */
    private static MockedStatic<DataMapper> dataMapperMock;

/**
    * Inizializza il mock statico del {@link DataMapper} prima dell'esecuzione di qualsiasi test.
    * <p>
    * Configura il comportamento di default dei metodi statici per restituire oggetti vuoti/dummy,
    * evitando eccezioni di parsing durante i test di I/O.
    */
   @BeforeAll
   static void globalSetupMocks() {
	   
	   ConfirmationStructure sampleCS = new ConfirmationStructure();
	   
       dataMapperMock = Mockito.mockStatic(DataMapper.class);
       dataMapperMock.when(() -> DataMapper.deserializeXmlOrderResponse(Mockito.anyString()))
       			.thenReturn(new XmlOrderResponse());
       dataMapperMock.when(() -> DataMapper.mapConfirmationFromXml(Mockito.any(XmlOrderResponse.class)))
		       .thenReturn(sampleCS);
   }

/**
    * Chiude il mock statico al termine di tutti i test della classe.
    * <p>
    * <b>Importante:</b> Questo passaggio è fondamentale per deregistrare il mock dal thread locale
    * ed evitare interferenze con altri test che potrebbero usare {@link DataMapper}.
    */
   @AfterAll
   static void globalTearDownMocks() {
       if (dataMapperMock != null) {
           dataMapperMock.close();
       }
   }
        
/**
    * Prepara l'ambiente del file system prima di ogni singolo test.
    * <p>
    * Crea la struttura delle cartelle (inbound, outbound, archived) all'interno della directory temporanea
    * e inizializza la configurazione {@link FTPConfig}.
    *
    * @throws Exception in caso di errori nella creazione delle directory.
    */
    @BeforeEach
    void setupTempDirectories() throws Exception {
        inbound = tempDir.resolve("inbound");
        outbound = tempDir.resolve("outbound");
        archived = tempDir.resolve("archived");

        Files.createDirectories(inbound);
        Files.createDirectories(outbound);
        Files.createDirectories(archived);

        cfg = new FTPConfig(inbound.toString(), outbound.toString(), archived.toString());
    }
    
/**
     * Verifica che {@link FTPReader#fetchConfirmations()} rilevi ed elabori correttamente i file XML.
     * <p>
     * Scenario:
     * <ul>
     * <li>Viene creato un file "CONF_SAMPLE.xml" nella directory outbound.</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>Il metodo ritorna {@code true} (file trovati).</li>
     * <li>Il buffer interno del reader contiene una {@link Confirmation}.</li>
     * <li>L'ID della conferma estratta corrisponde al nome del file originale.</li>
     * </ul>
     *
     * @throws Exception per errori di I/O.
     */
    @Test
    void testFetchConfirmations_readsXmlFiles() throws Exception {

        // crea un file .xml nella outbound
        String filename = "CONF_SAMPLE.xml";
        Path xmlFile = outbound.resolve(filename);
        String xmlContent = "<orderResponse><id>42</id></orderResponse>";
        Files.writeString(xmlFile, xmlContent, StandardCharsets.UTF_8);

        // Mock static DataMapper per isolare il test dalla logica di parsing/mapping

        FTPReader reader = new FTPReader(cfg);

        boolean found = reader.fetchConfirmations();
        assertTrue(found, "fetchConfirmations dovrebbe trovare almeno una confirmation nell'outbound");

        assertTrue(reader.hasConfirmation(), "dopo fetchConfirmations il buffer dovrebbe contenere conferme");
        Confirmation popped = reader.popConfirmation();
        assertNotNull(popped, "popConfirmation non dovrebbe restituire null");

        assertEquals(filename, popped.getConfirmationId(), "L'ID della confirmation deve corrispondere al nome del file letto");
        
    }
   
/**
     * Verifica che {@link FTPReader#fetchConfirmations()} ignori i file che non sono XML.
     * <p>
     * Scenario:
     * <ul>
     * <li>La directory outbound contiene file .txt, .json e sottocartelle, ma nessun .xml.</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>Il metodo ritorna {@code false}.</li>
     * <li>Il buffer interno del reader rimane vuoto.</li>
     * </ul>
     *
     * @throws Exception per errori di I/O.
     */
    @Test
    void testFetchConfirmations_returnsFalse_whenOutboundHasNoXmlFiles() throws Exception {

        // Alcuni file non-xml nella directory outbound
        Files.writeString(outbound.resolve("README.txt"), "This is a readme", StandardCharsets.UTF_8);
        Files.writeString(outbound.resolve("data.json"), "{\"k\":\"v\"}", StandardCharsets.UTF_8);
        Files.createDirectory(outbound.resolve("subdir")); // una sottocartella non dovrebbe essere conteggiata

        FTPReader reader = new FTPReader(cfg);

        boolean result = reader.fetchConfirmations();

        // Quando non ci sono .xml la funzione containsXmlFiles ritorna false e fetchConfirmations ritorna false
        assertFalse(result, "fetchConfirmations dovrebbe ritornare false quando non ci sono file .xml nella cartella outbound");
        assertFalse(reader.hasConfirmation(), "Il buffer non dovrebbe contenere conferme");
    }
}