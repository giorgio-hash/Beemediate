package com.beemediate.beemediate.infrastructure.ftp.mapper;

import java.util.Arrays;

import javax.xml.stream.XMLInputFactory;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;

import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlAddress;
import com.beemediate.beemediate.infrastructure.ftp.dto.confirmation.XmlOrderResponse;
import com.beemediate.beemediate.infrastructure.ftp.dto.confirmation.XmlOrderResponseInfo;
import com.beemediate.beemediate.infrastructure.ftp.dto.confirmation.XmlOrderResponseSummary;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlItem;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlOrder;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlOrderHeader;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlOrderSummary;
import com.ctc.wstx.stax.WstxInputFactory;
import com.ctc.wstx.stax.WstxOutputFactory;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.dataformat.xml.XmlFactory;
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
	private static final XmlMapper xmlMapper = initMapper();
	
	/**
	 * Costruttore private
	 */
	private DataMapper() {/*empty constructor*/}
	
	/**
	 * Inizializza istanza di XmlMapper disattivando la valutazione dei namespace. 
	 * Questa scelta è volta a semplificare l'implementazione degli adattatori FTP. Andrebbe ponderata una strategia che coinvolga XML-schema.
	 * @return XmlMapper
	 */
	private static XmlMapper initMapper() {
		// disattiva la risoluzione del namespace: 
		// https://github.com/FasterXML/jackson-dataformat-xml/issues/63
		XMLInputFactory f = new WstxInputFactory();
		f.setProperty(XMLInputFactory.IS_NAMESPACE_AWARE, Boolean.FALSE);
		return new XmlMapper(new XmlFactory(f, new WstxOutputFactory()));
	}
	
	/**
	 * Converte OrderStructure in una struttura serializzaibile.
	 * @param os - OrderStructure
	 * @return XmlOrder
	 */
	public static XmlOrder mapOrderToXml(OrderStructure os) {

		return new XmlOrder(
							new XmlOrderHeader(os.getHeader()),
							Arrays.stream(os.getItemList())
							          .map(XmlItem::new)
							          .toList(),
							new XmlOrderSummary(os.getOrderSummary())
							);
	}
	
	/**
	 * Serializza l'oggetto XmlOrder per ottenere la struttura dati ORDER.
	 * @param xo - XmlOrder
	 * @return String con l'ordine serializzato
	 */
	public static String serializeXmlOrder(XmlOrder xo) {
		try {
			return xmlMapper.writeValueAsString(xo);
		} catch (JsonProcessingException e) {
			e.printStackTrace();
		}
		
		return null;
	}
	
	/**
	 * Deserializza la struttura dati ORDERRESPONSE in un oggetto XmlOrderResponse.
	 * @param data - String contenente struttura serializzata
	 * @return XmlOrderResponse
	 */
	public static XmlOrderResponse deserializeXmlOrderResponse(String data) {
		
		try {
			return xmlMapper.readValue(data, XmlOrderResponse.class);
		}catch(JsonProcessingException e) {
			e.printStackTrace();
		}
		
		return null;
	}
	
	/**
	 * Mappa XmlOrderResponse nella struttura ConfirmationStructure, con dati di sintesi della conferma d'ordine.
	 * @param xor - XmlOrderResponse
	 * @return ConfirmationStructure
	 */
	public static ConfirmationStructure mapConfirmationFromXml(XmlOrderResponse xor) {
		
		ConfirmationStructure cs = new ConfirmationStructure();
		
		
		XmlOrderResponseInfo info = xor.getOrderResponseHeader()
										.getOrderResponseInfo();
		cs.setOrderResponseDate(info.getOrderResponseDate());
		cs.setDeliveryDate(info.getDeliveryDate()
								.getDeliveryEndDate());
		cs.setOrderId(info.getOrderId());
		cs.setOrderIdGealan(info.getSupplierOrderId());
		cs.setCurrency(info.getCurrency());
		
		
		XmlAddress addr = info.getParties()
								.get(0)
								.getAddress();
		cs.setAddressCity(addr.getCity());
		cs.setAddressCountry(addr.getCountry());
		cs.setAddressCountryCoded(addr.getCountryCoded());
		cs.setAddressName(addr.getName());
		cs.setAddressStreet(addr.getStreet());
		cs.setAddressZip(addr.getZip());
		
		
		XmlOrderResponseSummary summary = xor.getOrderSummary();
		cs.setTotalAmount(summary.getTotalAmount());
		cs.setTotalItemNum(summary.getTotalItemNum());
		
		return cs;
		
	}
	
}
