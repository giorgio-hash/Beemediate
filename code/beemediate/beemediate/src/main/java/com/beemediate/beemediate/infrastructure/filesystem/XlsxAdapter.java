package com.beemediate.beemediate.infrastructure.filesystem;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.core.io.Resource;
import org.springframework.core.io.ResourceLoader;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.domain.ports.infrastructure.filesystem.SupplierCatalogReaderPort;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;

/**
 * Adattatore di SupplierCatalogReaderPort per recuperare informazioni da sorgenti {@code .xlsx}.
 */
@Component
public class XlsxAdapter implements SupplierCatalogReaderPort{

	/**
	 * Logger
	 */
	private final Logger log = LoggerFactory.getLogger(XlsxAdapter.class);
	
	/**
	 * ResourceLoader
	 */
    private final ResourceLoader resourceLoader;
    
    /**
     * Percorso al file {@code .xlsx}
     */
    private static final String RESOURCE_PATH = "classpath:data/MasterData_IT.XLSX";

    /**
     * Costruttore
     * @param resourceLoader - oggetto ResourceLoader
     */
    @Autowired
    public XlsxAdapter(final ResourceLoader resourceLoader) {
        this.resourceLoader = resourceLoader;
    }

    @Override
    public String[] readArticleNumbers() {
        try {
            final List<String> numbers = extractArticleNumbers();
            return numbers.toArray(new String[0]);
        } catch (IOException | IllegalArgumentException e) {
            log.error("Errore durante la lettura del file XLSX", e);
            return new String[0];
        }
    }

    /**
     * Estrae la prima colonna del file {@code .xlsx}, contenente i numeri articolo
     * @return List di elementi String
     * @throws IOException se ci sono problemi nel recupero del file
     * @throws IllegalArgumentException se il file è vuoto
     */
    private List<String> extractArticleNumbers() throws IOException {
        final List<String> numeriArticolo = new ArrayList<>();

        final Resource resource = resourceLoader.getResource(RESOURCE_PATH);
        try (InputStream is = resource.getInputStream();
             Workbook workbook = new XSSFWorkbook(is)) {

            final Sheet sheet = workbook.getSheetAt(0);
            final int headerRowNum = sheet.getFirstRowNum();

            if (headerRowNum == -1) {
                throw new IllegalArgumentException ("File cannot be null or empty");
            }

            for (int i=sheet.getFirstRowNum()+1; i<=sheet.getLastRowNum(); i++) {
            	numeriArticolo.add(sheet.getRow(i).getCell(0).getStringCellValue());
            }
        }

        return numeriArticolo;
    }
}
