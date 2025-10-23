package com.beemediate.beemediate.infrastructure.ftp;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Stack;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.ConfirmationProviderPort;
import com.beemediate.beemediate.infrastructure.ftp.config.FTPConfig;
import com.beemediate.beemediate.infrastructure.ftp.exceptions.WrongPathException;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;

/**
 * Adattatore di ConfirmationProviderPort. Contiene le funzioni per
 * <ul>
 * <li>Rilevare le strutture dati "in arrivo" sul FTP;</li>
 * <li>Deserializzare e mappare le strutture dati in oggetti utili al dominio.</li>
  *</ul>
 * Una volta mappate, le strutture dati vengono caricate in un buffer che verrà consumato dal dominio.
 * 
 */
@Component
public class FTPReader implements ConfirmationProviderPort{

	/**
	 * Logger
	 */
	private final Logger log = LoggerFactory.getLogger(FTPReader.class);

	/**
	 * oggetto di configurazione del filesystem FTP
	 */
	private final FTPConfig ftp;
	
	/**
	 * buffer con logica LIFO per le strutture dati sintetiche delle conferme d'ordine (Confirmation)
	 */
	private final Stack<Confirmation> buffer = new Stack<>();
	
    /**
     * Costruttore
     * @param ftp - bean di configurazione FTPConfig
     */
    @Autowired 
	public FTPReader(FTPConfig ftp) {
		this.ftp = ftp;
	}
	
	
    @Override
    public Confirmation popConfirmation() {
    	return  buffer.pop();
    }
    
    
    @Override
    public boolean hasConfirmation() {
    	return !buffer.isEmpty();
    }
    
    
    @Override
	public boolean fetchConfirmations() {
		
		final Path outboundPath = Path.of(ftp.getOutboundFolder());
		
		try {
			if(!containsXmlFiles(outboundPath))
				return false;
			
			buffer.clear();
			
			String or;
			Confirmation c;
			
			for(Path p : collectXmlFiles(outboundPath)) {
				
				or = Files.readString(p, StandardCharsets.UTF_8);
				log.info(or);
				
				c = new Confirmation( 
							p.getFileName().toString(),
							DataMapper.mapConfirmationFromXml(
									DataMapper.deserializeXmlOrderResponse(or)
									)
						);
				
				buffer.add(c);
			}
			
			return hasConfirmation();
		} catch (IOException | WrongPathException e) {
			log.error("Errore durante l'estrazione delle conferme.",e);
		}
		
		return false;
	}
	
	
    /**
     * Trova tutti i file con estensione ".xml" nella directory (non nelle sottodirectory).
     *
     * @param directoryPath percorso della directory da scandire
     * @return lista di Path dei file .xml trovati
     * @throws IOException se si verifica un errore I/O
     * @throws WrongPathException se il percorso non è una directory valida
     */
    private List<Path> collectXmlFiles(Path directoryPath) throws IOException, WrongPathException {
        // Verifica che il percorso esista ed sia una directory
        if (!Files.exists(directoryPath) || !Files.isDirectory(directoryPath)) {
            throw new WrongPathException("Il percorso specificato non è una directory valida: " + directoryPath);
        }

        try (Stream<Path> walk = Files.walk(directoryPath)) {
            return walk
                    .filter(Files::isRegularFile)          // solo file "normali"
                    .filter(path -> path.toString().toLowerCase().endsWith(".xml"))  // estensione .xml
                    .collect(Collectors.toList());
        }
    }
    
    
    /**
     * Verifica se in una directory è presente almeno un file con estensione ".xml".
     *
     * @param directoryPath percorso della directory da controllare
     * @return true se esiste almeno un file .xml, false altrimenti
     * @throws IOException se si verifica un errore di I/O o se il percorso non è una directory
     * @throws WrongPathException se il percorso non è una directory valida
     */
    private boolean containsXmlFiles(Path directoryPath) throws IOException, WrongPathException {
        // Verifica che il percorso esista e sia una directory
        if (!Files.exists(directoryPath) || !Files.isDirectory(directoryPath)) {
            throw new WrongPathException("Il percorso specificato non è una directory valida: " + directoryPath);
        }

        // Usa uno stream per cercare file .xml
        try (Stream<Path> files = Files.list(directoryPath)) {
            return files
                    .filter(Files::isRegularFile)
                    .anyMatch(path -> path.toString().toLowerCase().endsWith(".xml"));
        }
    }
}
