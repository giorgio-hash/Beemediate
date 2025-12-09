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
 * Test per FTPWriter. Usa filesystem temporanei (@TempDir) e mocking statico di DataMapper.
 */
public class FTPWriterTest {
	
    @TempDir
    Path tempDir;

    private Path inbound;
    private Path outbound;
    private Path archived;
    private FTPConfig cfg;
    
    private static MockedStatic<DataMapper> dataMapperMock;
    
    
    @BeforeAll
    static void globalSetupMocks() {
 	   
 	  String expectedContent = "<order><id>ORD-123</id></order>";
 	   
 	 dataMapperMock = Mockito.mockStatic(DataMapper.class);
 	  
       dataMapperMock.when(() -> DataMapper.mapOrderToXml(Mockito.any(OrderStructure.class)))
       		.thenReturn(new XmlOrder());
       dataMapperMock.when(() -> DataMapper.serializeXmlOrder(Mockito.any(XmlOrder.class)))
       		.thenReturn(expectedContent);
    }

    @AfterAll
    static void globalTearDownMocks() {
        if (dataMapperMock != null) {
            dataMapperMock.close();
        }
    }
    
    
    
    
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