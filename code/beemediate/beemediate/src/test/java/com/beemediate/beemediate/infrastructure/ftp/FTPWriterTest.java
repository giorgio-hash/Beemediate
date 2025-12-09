package com.beemediate.beemediate.infrastructure.ftp;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import java.util.stream.Stream;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.mockito.MockedStatic;
import org.mockito.Mockito;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.infrastructure.ftp.config.FTPConfig;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlOrder;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;

/**
 * Test per la classe {@link FTPWriter}. Usa filesystem temporanei (@TempDir) e mocking statico di DataMapper.
 * <p>
 * Verifica le operazioni di scrittura e gestione dei file sul filesystem:
 * <ul>
 * <li>Scrittura di nuovi ordini nella cartella {@code inbound}.</li>
 * <li>Archiviazione (spostamento) delle conferme dalla cartella {@code outbound} alla cartella {@code archived}.</li>
 * </ul>
 * Utilizza {@link TempDir} per creare un ambiente isolato e {@link MockedStatic} per astrarre la logica di mapping.
 */
public class FTPWriterTest {
	
    /** Directory temporanea gestita da JUnit, ricreata per ogni esecuzione o classe. */
    @TempDir
    Path tempDir;

    private Path inbound;
    private Path outbound;
    private Path archived;
    private FTPConfig cfg;
    
    /** Mock statico per {@link DataMapper}, necessario per evitare la vera serializzazione XML durante i test di I/O. */
    private static MockedStatic<DataMapper> dataMapperMock;
    
/**
     * Configurazione globale dei mock statici.
     * <p>
     * Intercetta le chiamate a {@link DataMapper} per restituire una stringa XML fissa ("<order>..."),
     * garantendo che i test verifichino solo la scrittura del file e non la correttezza del contenuto XML.
     */
    @BeforeAll
    static void globalSetupMocks() {
 	   
 	  String expectedContent = "<order><id>ORD-123</id></order>";
 	   
 	 dataMapperMock = Mockito.mockStatic(DataMapper.class);
 	  
       dataMapperMock.when(() -> DataMapper.mapOrderToXml(Mockito.any(OrderStructure.class)))
       		.thenReturn(new XmlOrder());
       dataMapperMock.when(() -> DataMapper.serializeXmlOrder(Mockito.any(XmlOrder.class)))
       		.thenReturn(expectedContent);
    }

/**
     * Chiude il mock statico al termine dei test per liberare le risorse.
     */
    @AfterAll
    static void globalTearDownMocks() {
        if (dataMapperMock != null) {
            dataMapperMock.close();
        }
    }
    
/**
     * Prepara la struttura delle directory temporanee prima di ogni test.
     * <p>
     * Crea fisicamente le cartelle {@code inbound}, {@code outbound} e {@code archived}
     * all'interno della directory temporanea di test.
     *
     * @throws Exception in caso di errori di creazione directory.
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
     * Verifica che {@link FTPWriter#loadOrder(Order)} scriva correttamente il file su disco.
     * <p>
     * Scenario:
     * <ul>
     * <li>Viene passato un ordine mockato.</li>
     * <li>Il {@link DataMapper} (mockato) restituisce un contenuto XML predefinito.</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>Il metodo ritorna {@code true}.</li>
     * <li>Nella cartella {@code inbound} viene creato un file che inizia con "ORDER__" e finisce con ".xml".</li>
     * <li>Il contenuto del file corrisponde esattamente alla stringa XML attesa.</li>
     * </ul>
     *
     * @throws Exception per errori di I/O.
     */
    @Test
    void testLoadOrder_createsFile() throws Exception {

        FTPWriter writer = new FTPWriter(cfg);


        OrderStructure sampleOS = new OrderStructure();

        // contenuto scritto nel file
        String expectedContent = "<order><id>ORD-123</id></order>";


            Order mockOrder = Mockito.mock(Order.class);
            Mockito.when(mockOrder.getData()).thenReturn(sampleOS);


            boolean result = writer.loadOrder(mockOrder);
            assertTrue(result, "loadOrder dovrebbe ritornare true se il file è stato scritto correttamente");

            // cerca tra i file della inbound quello creato (ORDER__*.xml)
            try (Stream<Path> list = Files.list(inbound)) {
                Optional<Path> created = list
                        .filter(p -> p.getFileName().toString().startsWith("ORDER__") && p.toString().toLowerCase().endsWith(".xml"))
                        .findFirst();
                assertTrue(created.isPresent(), "Dovrebbe essere stato creato un file ORDER__*.xml nella cartella inbound");

                String actual = Files.readString(created.get(), StandardCharsets.UTF_8);
                assertEquals(expectedContent, actual, "Il contenuto del file deve corrispondere alla serializzazione fornita");
            }
    }

/**
     * Verifica che {@link FTPWriter#archive(Confirmation)} sposti il file nella cartella di archivio.
     * <p>
     * Scenario:
     * <ul>
     * <li>Esiste un file di conferma nella cartella {@code outbound}.</li>
     * <li>Viene invocato il metodo archive passando l'oggetto Confirmation corrispondente.</li>
     * </ul>
     * Risultato atteso:
     * <ul>
     * <li>Il file non esiste più nella cartella {@code outbound}.</li>
     * <li>Il file esiste ora nella cartella {@code archived}.</li>
     * </ul>
     *
     * @throws Exception per errori di I/O.
     */
    @Test
    void testArchive_movesFile() throws Exception {

        cfg = new FTPConfig(inbound.toString(), outbound.toString(), archived.toString());
        cfg.verifyDirectories();


        String filename = "CONF__2025_11_18_10_00_00.xml";
        Path src = outbound.resolve(filename);
        Files.writeString(src, "<confirmation/>", StandardCharsets.UTF_8);

        FTPWriter writer = new FTPWriter(cfg);


        Confirmation mockConf = Mockito.mock(Confirmation.class);
        Mockito.when(mockConf.getConfirmationId()).thenReturn(filename);

        boolean moved = writer.archive(mockConf);

        assertTrue(moved, "archive dovrebbe ritornare true dopo lo spostamento riuscito");
        assertFalse(Files.exists(src), "Il file sorgente non dovrebbe più esistere nella directory outbound");
        Path target = archived.resolve(filename);
        assertTrue(Files.exists(target), "Il file dovrebbe esistere nella cartella archived dopo lo spostamento");
    }
    
/**
     * Verifica la gestione degli errori (IOException) durante la scrittura dell'ordine.
     * <p>
     * Utilizza un ulteriore {@link MockedStatic} sulla classe {@link Files} per simulare
     * un fallimento critico del filesystem (es. disco pieno o permessi negati).
     *
     * @throws Exception non attesa, l'eccezione deve essere catturata internamente.
     */
    @Test
    void testLoadOrder_returnsFalse_whenIOExceptionDuringCreateDirectories() {

        FTPWriter writer = new FTPWriter(cfg);

        OrderStructure sampleOS = new OrderStructure();

        // mock static DataMapper per mantenere la serializzazione costante

            Order mockOrder = Mockito.mock(Order.class);
            Mockito.when(mockOrder.getData()).thenReturn(sampleOS);

            try (MockedStatic<Files> filesMock = Mockito.mockStatic(Files.class)) {

                filesMock.when(() -> Files.createDirectories(inbound)).thenThrow(new IOException("Simulated IO error"));

                boolean result = writer.loadOrder(mockOrder);

                assertFalse(result, "loadOrder dovrebbe ritornare false quando si verifica un IOException durante la scrittura");
            }
    }
}