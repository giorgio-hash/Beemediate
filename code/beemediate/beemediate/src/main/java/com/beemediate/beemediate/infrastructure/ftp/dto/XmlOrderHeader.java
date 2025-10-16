package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per header ordine, contenente informazioni sulla transazione. Può prendere in input il POJO {@code OrderHeader}
 */
@JacksonXmlRootElement(localName = "ORDER_HEADER")
public class XmlOrderHeader {
	
	/**
	 * Riferimento a DTO XmlOrderInfo per ORDER_INFO.
	 */
	@JacksonXmlProperty(localName="ORDER_INFO")
	private XmlOrderInfo orderInfo;

	/**
	 * Costruttore per creare struttura XML-OpenTrans header ordine partendo dal POJO {@code OrderHeader}
	 * @param head - OrderHeader
	 */
	public XmlOrderHeader(OrderHeader head) {
		super();
		this.orderInfo = new XmlOrderInfo( head );
	}

	/**
	 * 
	 * @return XmlOrderInfo
	 */
	public XmlOrderInfo getOrderInfo() {
		return orderInfo;
	}

	
}
