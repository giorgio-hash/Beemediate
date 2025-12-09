package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.fasterxml.jackson.annotation.JsonInclude;
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
	 * Rifeirmento a DTO XmlAgreement per AGREEMENT
	 */
	@JacksonXmlProperty(localName="AGREEMENT")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlAgreement agreement;
	
	/**
	 * empty constructor for deserializer
	 */
	public XmlOrderHeader() {/*empty constructor*/}
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans header ordine partendo dal POJO {@code OrderHeader}
	 * @param head - OrderHeader
	 */
	public XmlOrderHeader(final OrderHeader head) {
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

	public XmlAgreement getAgreement() {
		return agreement;
	}

	public void setAgreement(final XmlAgreement agreement) {
		this.agreement = agreement;
	}

	public void setOrderInfo(final XmlOrderInfo orderInfo) {
		this.orderInfo = orderInfo;
	}

	
}
