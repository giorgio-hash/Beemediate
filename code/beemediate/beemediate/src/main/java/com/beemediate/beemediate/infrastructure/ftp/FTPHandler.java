package com.beemediate.beemediate.infrastructure.ftp;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.PropertySource;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;

/**
 * Adattatore di FTPHandlerPort che tratta la gestione dei file XML nel sistema FTP. 
 * Nello specifico, tratta 
 * <ul>
 * <li>la serializzazione POJO a XML-OpenTrans</li>
 * <li> il posizionamento delle strutture dati nel filesystem destinato alla comunicazione tra i partner commerciali</li> 
 * </ul>
 * Questo adattatore <b><u>non tratta il protocollo di comunicazione FTP</u></b>, bensì tratta le strutture dati trasmesse e ricevute sul sistema dedicato.
 */
@Component
@PropertySource("classpath:ftpconfig.properties")
public class FTPHandler implements FTPHandlerPort{

	/**
	 * Riferimento al Logger della classe
	 */
	private final Logger log = LoggerFactory.getLogger(FTPHandler.class);
	
	/**
	 * Folder contenente gli ordini da mandare al fornitore
	 */
	private final String inbound;
	/**
	 * Folder contenente le conferme ricevute dal fornitore
	 */
	private final String outbound;
	/**
	 * Folder contenente le conferme archiviate. Una conferma diventa <i>archiviata</i> dopo esser stata individuata ed analizzata.
	 */
	private final String archived;
	
	/**
	 * Formattazione DateTime
	 */
    private static final DateTimeFormatter FORMATTER = DateTimeFormatter.ofPattern("yyyy_MM_dd_HH_mm_ss");
	
	/**
	 * Crea una istanza di {@code FTPHandler} utilizzando i dati presenti in {@code resources/ftpconfig.properties}, obbligatoriamente presente nel progetto. In assenza di valori personalizzati, vengono applicati dei valori di default.
	 * @param inbound - valore della chiave {@code file.inbound}, se presente (default: <i>"ftp/INBOUND"</i>)
	 * @param outbound - valore della chiave {@code file.outbound}, se presente (default <i>"ftp/OUTBOUND"</i>)
	 * @param archived - valore della chiave {@code file.archived}, se presente (default: <i>"ftp/OUTBOUND/ARCHIV"</i>)
	 */
	public FTPHandler(@Value("${file.inbound:ftp/INBOUND}") final String inbound,
						@Value("${file.outbound:ftp/OUTBOUND}") final String outbound,
						@Value("${file.archived:ftp/OUTBOUND/ARCHIV}") final String archived
						) {

		this.inbound = inbound;
		this.outbound = outbound;
		this.archived = archived;
	}
	
	
	@Override
	public boolean archive(final Confirmation c) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}


	@Override
	public boolean loadOrder(final Order o) {
		return loadOrder(o.getData());
	}

	/**
	 * Converte il POJO {@code OrderStructure} in una struttura <i>Serializable</i>, per poi salvare la struttura dati su file {@code .xml}, conforme al formato XML-OpenTrans, al percorso specificato da <i>inbound</i>
	 * @param os - oggetto {@code OrderStructure}
	 * @return <i>true</i> se l'operazione è andata a buon fine
	 */
	private boolean loadOrder(final OrderStructure os) {
		
		
		final String content = DataMapper.mapToXml(os);
		final String fileName = new StringBuilder()
										.append("ORDER__")
										.append(LocalDateTime.now().format(FORMATTER))
										.append(".xml")
										.toString();
		
		final Path filePath = Paths.get(inbound, fileName); 
		 
		return writeToInbound(content, filePath);
	}
	
	
	/**
	 * Al percorso <i>filePath</i>, crea un nuovo file scrivendoci <i>content</i>.
	 * @param content - String da scrivere
	 * @param filePath - {@code Path} indicante il percorso al file creato
	 * @return <i>true</i> se l'operazione è andata a buon fine
	 */
	private boolean writeToInbound(final String content, final Path filePath) {
		
        try {
            // Crea la directory se non esiste
            Files.createDirectories(filePath.getParent());

            // Scrive il contenuto nel file (sovrascrive se esiste)
            Files.write(filePath, content.getBytes(StandardCharsets.UTF_8),
                        StandardOpenOption.CREATE,
                        StandardOpenOption.TRUNCATE_EXISTING);

            log.info("File scritto con successo: {}", filePath.toAbsolutePath().toString().replaceAll("[\r\n]","") );
        } catch (IOException e) {
        	log.error("Problema di scrittura sul filesystem:".concat(filePath.toAbsolutePath().toString().replaceAll("[\r\n]","") ),e);
        }
        return Files.exists(filePath);
	}

	/**
	 * 
	 * @return String indicante il percorso dove vengono depositati i file degli ordini. <br>Default: <i>"ftp/INBOUND"</i>
	 */
	public String getInbound() {
		return inbound;
	}

	/**
	 * 
	 * @return String indicante il percorso dove recuperati i file delle conferme. <br>Default: <i>"ftp/OUTBOUND"</i>
	 */
	public String getOutbound() {
		return outbound;
	}

	/**
	 * 
	 * @return String indicante il percorso dove archiviati i file delle conferme.<br>Default: <i>"ftp/OUTBOUND/ARCHIV"</i>
	 */
	public String getArchived() {
		return archived;
	}
	
	
	
}
