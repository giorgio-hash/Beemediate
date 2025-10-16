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
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.PropertySource;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;

@Component
@PropertySource("classpath:ftpconfig.properties")
public class FTPHandler implements FTPHandlerPort{

	
	private final Logger log = LoggerFactory.getLogger(FTPHandler.class);
	
	private final String inbound;
	private final String outbound;
	private final String archived;
	
    private static final DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy_MM_dd_HH_mm_ss");
	
	
	public FTPHandler(@Value("${file.inbound:ftp/INBOUND}") String inbound,
						@Value("${file.outbound:ftp/OUTBOUND}") String outbound,
						@Value("${file.archived:ftp/OUTBOUND/ARCHIV}") String archived
						) {

		this.inbound = inbound;
		this.outbound = outbound;
		this.archived = archived;
	}
	
	
	@Override
	public boolean archive(Confirmation c) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}

	@Override
	public boolean delete(Confirmation c) {
		throw new UnsupportedOperationException("Not implemented yet.");
	}

	@Override
	public boolean loadOrder(Order o) {
		return loadOrder(o.getData());
	}

	
	private boolean loadOrder(OrderStructure os) {
		
		
		String content = DataMapper.mapToXml(os);
		String fileName = new StringBuilder()
							.append("ORDER__")
							.append(LocalDateTime.now().format(formatter)										)
							.append(".xml")
							.toString();
		
		Path filePath = Paths.get(inbound, fileName); 
		 
		return writeToInbound(content, filePath);
	}
	
	
	
	private boolean writeToInbound(String content, Path filePath) {
		
        try {
            // Crea la directory se non esiste
            Files.createDirectories(filePath.getParent());

            // Scrive il contenuto nel file (sovrascrive se esiste)
            Files.write(filePath, content.getBytes(StandardCharsets.UTF_8),
                        StandardOpenOption.CREATE,
                        StandardOpenOption.TRUNCATE_EXISTING);

            log.info("File scritto con successo: {}", filePath.toAbsolutePath());
        } catch (IOException e) {
        	log.info("Problema di scrittura sul filesystem:".concat(filePath.toAbsolutePath().toString()),e);
        }
        return Files.exists(filePath);
	}
	
}
