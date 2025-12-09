package com.beemediate.beemediate.infrastructure.ftp.config;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.After;
import org.junit.Test;

import com.beemediate.beemediate.infrastructure.ftp.exceptions.WrongPathException;

/**
 * Test JUnit4 per FTPConfig.
 *
 * Test:
 * - verifyDirectories ha successo quando tutti i percorsi sono directory esistenti
 * - verifyDirectories lancia WrongPathException quando un percorso non esiste
 * - verifyDirectories lancia WrongPathException quando un percorso è un file normale (non una directory)
 * - i metodi getter restituiscono gli stessi valori stringa passati al costruttore
 */
public class FTPConfigTest {

    /** temporary resources created by tests; cleaned in tearDown*/
    private Path tempDir1;
    /** temporary resources created by tests; cleaned in tearDown*/
    private Path tempDir2;
    /** temporary resources created by tests; cleaned in tearDown*/
    private Path tempDir3;
    /** temporary resources created by tests; cleaned in tearDown*/
    private Path tempFile;

    /**
     * Pulisce le risorse temporanee create dal test.
     * Elimina il file temporaneo (se presente) e le directory temporanee tempDir1/2/3
     * ricorsivamente, impostando i riferimenti a null. Viene eseguito dopo ogni test
     * (metodo annotato con @After).
     *
     * @throws IOException se si verificano errori durante l'eliminazione dei file o delle directory
     */
    @After
    public void tearDown() throws IOException {
        // cleanup if created
        if (tempFile != null && Files.exists(tempFile)) {
            Files.delete(tempFile);
            tempFile = null;
        }
        if (tempDir1 != null && Files.exists(tempDir1)) {
            Files.walk(tempDir1)
                    .map(Path::toFile)
                    .forEach(File::delete);
            tempDir1 = null;
        }
        if (tempDir2 != null && Files.exists(tempDir2)) {
            Files.walk(tempDir2)
                    .map(Path::toFile)
                    .forEach(File::delete);
            tempDir2 = null;
        }
        if (tempDir3 != null && Files.exists(tempDir3)) {
            Files.walk(tempDir3)
                    .map(Path::toFile)
                    .forEach(File::delete);
            tempDir3 = null;
        }
    }

    /**
     * Verifica che, con le directory di inbound/outbound/archived esistenti,
     * il metodo verifyDirectories() non sollevi eccezioni e che i getter
     * restituiscano esattamente i percorsi forniti al costruttore.
     *
     * @throws Exception se la creazione delle directory temporanee fallisce
     */
    @Test
    public void verifyDirectories_allExist_noExceptionAndGettersMatch() throws Exception {
        tempDir1 = Files.createTempDirectory("ftp-inbound-");
        tempDir2 = Files.createTempDirectory("ftp-outbound-");
        tempDir3 = Files.createTempDirectory("ftp-archived-");

        final String p1 = tempDir1.toAbsolutePath().toString();
        final String p2 = tempDir2.toAbsolutePath().toString();
        final String p3 = tempDir3.toAbsolutePath().toString();

        FTPConfig cfg = new FTPConfig(p1, p2, p3);

        // should not throw
        cfg.verifyDirectories();

        // getters must return original strings
        assertEquals(p1, cfg.getInboundFolder());
        assertEquals(p2, cfg.getOutboundFolder());
        assertEquals(p3, cfg.getArchivedFolder());
    }

    /**
     * Verifica che il metodo {@link FTPConfig#verifyDirectories()} sollevi un'eccezione
     * {@link WrongPathException} quando viene configurato un percorso di directory non esistente.
     * <p>
     * Scenario del test:
     * <ul>
     * <li>Vengono create due directory temporanee valide (inbound e outbound).</li>
     * <li>Viene creato un percorso per la directory di archiviazione che punta a una risorsa
     * cancellata (quindi non esistente su disco).</li>
     * </ul>
     * <p>
     * Risultato atteso: Il metodo di validazione deve fallire rilevando l'assenza della directory.
     *
     * @throws Exception se si verificano errori di I/O durante la preparazione dei file temporanei.
     */
    @Test(expected = WrongPathException.class)
    public void verifyDirectories_nonExistentPath_throwsWrongPathException() throws Exception {
        tempDir1 = Files.createTempDirectory("ftp-inbound-");
        tempDir2 = Files.createTempDirectory("ftp-outbound-");
        // create a path that does not exist and ensure it's removed
        Path nonExistent = Files.createTempDirectory("toDelete-");
        Files.delete(nonExistent);

        final String p1 = tempDir1.toAbsolutePath().toString();
        final String p2 = tempDir2.toAbsolutePath().toString();
        final String p3 = nonExistent.toAbsolutePath().toString(); // does not exist

        FTPConfig cfg = new FTPConfig(p1, p2, p3);

        // should throw because archived path does not exist
        cfg.verifyDirectories();
    }

    /**
 * Verifica che {@link FTPConfig#verifyDirectories()} sollevi {@link WrongPathException}
 * quando un percorso configurato punta a un file anziché a una directory.
 *
 * @throws Exception per errori nella creazione delle risorse temporanee.
 */
    @Test(expected = WrongPathException.class)
    public void verifyDirectories_fileNotDirectory_throwsWrongPathException() throws Exception {
        tempDir1 = Files.createTempDirectory("ftp-inbound-");
        tempDir2 = Files.createTempDirectory("ftp-outbound-");
        // create a temporary file (not a directory)
        tempFile = Files.createTempFile("ftp-file-", ".tmp");

        final String p1 = tempDir1.toAbsolutePath().toString();
        final String p2 = tempDir2.toAbsolutePath().toString();
        final String p3 = tempFile.toAbsolutePath().toString(); // path points to a file

        FTPConfig cfg = new FTPConfig(p1, p2, p3);

        // should throw because archived path is not a directory
        cfg.verifyDirectories();
    }
}