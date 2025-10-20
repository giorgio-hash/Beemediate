package com.beemediate.beemediate.infrastructure.ftp.mapper;

import java.util.Arrays;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;

import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlItem;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrder;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrderHeader;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrderSummary;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.dataformat.xml.XmlMapper;

/**
 * Classe utility per mappare gli oggetti POJO del dominio con le strutture XML. A tale scopo, la classe si serve delle classi con prefisso "Xml" presenti in <i>com.beemediate.beemediate.infrastructure.ftp.dto</i>.
 */
public class DataMapper {

	
	private static final Logger log = LoggerFactory.getLogger(DataMapper.class);
	
	/**
	 * Oggetto Jackson per gestire serializzazione/deserializzazione tra strutture dati XML e DTO.
	 */
	@Autowired
	private static XmlMapper xmlMapper = new XmlMapper();
	
	
	/**
	 * Converte il POJO OrderStructure in una struttura dati XML serializzata, servendosi della classe {@code XmlMapper} fornita da Jackson e dei DTO presenti in <i>beemediate.beemediate.infrastructure.ftp.dto</i>.
	 * @param os - OrderStructure
	 * @return String - oggetto {@code XmlOrder } serializzato
	 */
	public static String mapToXml(final OrderStructure os) {
		
		try {
			return xmlMapper.writeValueAsString(
								new XmlOrder(
										new XmlOrderHeader(os.getHeader()),
										Arrays.stream(os.getItemList())
								          		.map(XmlItem::new)
								          		.toList(),
										new XmlOrderSummary(os.getOrderSummary())												)
										);
		} catch (JsonProcessingException e) {
			log.error("Errore nel mapping XML",e);
		}
		return null;
	}
	
}
