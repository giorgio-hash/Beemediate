package com.beemediate.beemediate.infrastructure.ftp.config;

import java.io.File;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.PropertySource;

import com.beemediate.beemediate.infrastructure.ftp.exceptions.WrongPathException;

import jakarta.annotation.PostConstruct;

/**
 * Classe di configurazione del sistema di cartelle FTP
 */
@Configuration
@PropertySource("classpath:ftpconfig.properties")
public class FTPConfig {

	/**
	 * Nome folder contenente gli ordini da mandare al fornitore
	 */
	private final String inboundFolder;
	/**
	 * Nome folder contenente le conferme ricevute dal fornitore
	 */
	private final String outboundFolder;
	/**
	 * Nome folder contenente le conferme archiviate. Una conferma diventa <i>archiviata</i> dopo esser stata individuata ed analizzata.
	 */
	private final String archivedFolder;

	/**
	 * Crea il bean di configurazione del fileystem del FTP utilizzando i dati presenti in {@code resources/ftpconfig.properties}. In assenza di valori personalizzati, vengono applicati dei valori di default.
	 * @param inbound - valore della chiave {@code file.inbound}, se presente (default: <i>"ftp/INBOUND"</i>)
	 * @param outbound - valore della chiave {@code file.outbound}, se presente (default <i>"ftp/OUTBOUND"</i>)
	 * @param archived - valore della chiave {@code file.archived}, se presente (default: <i>"ftp/OUTBOUND/ARCHIV"</i>)
	 */
    public FTPConfig(
            @Value("${file.inbound:ftp/INBOUND}") String inbound,
            @Value("${file.outbound:ftp/OUTBOUND}") String outbound,
            @Value("${file.archived:ftp/OUTBOUND/ARCHIV}") String archived) {
        this.inboundFolder = inbound;
        this.outboundFolder = outbound;
        this.archivedFolder = archived;
    }

    /**
     * Verifica e crea le directory dopo l'inizializzazione del bean.
     * @throws WrongPathException 
     */
    @PostConstruct
    public void verifyDirectories() throws WrongPathException {
        check(inboundFolder);
        check(outboundFolder);
        check(archivedFolder);
    }

    /**
     * Verifica che il percorso sia una directory esistente
     * @param path - String indicante il percorso da verificare
     * @throws WrongPathException - path non è una directory
     */
    private void check(String path) throws WrongPathException {
        File dir = new File(path);
        if (!dir.exists() || !dir.isDirectory())
            throw new WrongPathException("Il path \""+ path +"\" non porta ad una directory.");
    }
    
    /**
     * 
     * @return String rappresentante la folder dei messaggi verso il fornitore
     */
    public String getInboundFolder() {
        return inboundFolder;
    }
    
    /**
     * 
     * @return String rappresentante la folder dei messaggi in arrivo dal fornitore
     */
    public String getOutboundFolder() {
        return outboundFolder;
    }

    /**
     * 
     * @return String rappresentante la folder dei messaggi archiviati
     */
    public String getArchivedFolder() {
        return archivedFolder;
    }
}