package com.beemediate.beemediate.infrastructure.odoo.config;

import com.beemediate.beemediate.infrastructure.ftp.config.FTPConfig;
import com.beemediate.beemediate.infrastructure.ftp.exceptions.WrongPathException;
import org.junit.After;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.*;

/**
 * JUnit4 tests for FTPConfig.
 *
 * Tests:
 * - verifyDirectories succeeds when all paths are existing directories
 * - verifyDirectories throws WrongPathException when a path does not exist
 * - verifyDirectories throws WrongPathException when a path is a regular file (not a directory)
 * - getters return the same string values passed to constructor
 */
public class FTPConfigTest {

    // temporary resources created by tests; cleaned in tearDown
    private Path tempDir1;
    private Path tempDir2;
    private Path tempDir3;
    private Path tempFile;

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