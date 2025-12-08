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
 * Test per FTPReader. Usa MockedStatic per DataMapper e istanze reali di ConfirmationStructure (mock ben fatto).
 */
public class FTPReaderTest {
	
    @TempDir
    Path tempDir;

    private Path inbound;
    private Path outbound;
    private Path archived;
    private FTPConfig cfg;
    
    private static MockedStatic<DataMapper> dataMapperMock;

   @BeforeAll
   static void globalSetupMocks() {
	   
	   ConfirmationStructure sampleCS = new ConfirmationStructure();
	   
       dataMapperMock = Mockito.mockStatic(DataMapper.class);
       dataMapperMock.when(() -> DataMapper.deserializeXmlOrderResponse(Mockito.anyString()))
       			.thenReturn(new XmlOrderResponse());
       dataMapperMock.when(() -> DataMapper.mapConfirmationFromXml(Mockito.any(XmlOrderResponse.class)))
		       .thenReturn(sampleCS);
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