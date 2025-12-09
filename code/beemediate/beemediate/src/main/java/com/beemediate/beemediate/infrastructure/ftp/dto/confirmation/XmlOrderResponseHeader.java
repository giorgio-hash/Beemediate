package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Intestazione della conferma d'ordine XML
 */
@JacksonXmlRootElement(localName = "ORDERRESPONSE_HEADER")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseHeader {
	
	/**
	 * Informazioni di controllo sulla generazione del documento
	 */
	@JacksonXmlProperty(localName="CONTROL_INFO")
	private XmlControlInfo controlInfo;
	
	/**
	 * Informazioni della transazione
	 */
	@JacksonXmlProperty(localName="ORDERRESPONSE_INFO")
	private XmlOrderResponseInfo orderResponseInfo;

	/**
	 * 
	 * @return XmlControlInfo
	 */
	public XmlControlInfo getControlInfo() {
		return controlInfo;
	}

	/**
	 * 
	 * @param controlInfo - XmlControlInfo
	 */
	public void setControlInfo(final XmlControlInfo controlInfo) {
		this.controlInfo = controlInfo;
	}

	/**
	 * 
	 * @return XmlOrderResponseInfo
	 */
	public XmlOrderResponseInfo getOrderResponseInfo() {
		return orderResponseInfo;
	}

	/**
	 * 
	 * @param orderResponseInfo - XmlOrderResponseInfo
	 */
	public void setOrderResponseInfo(final XmlOrderResponseInfo orderResponseInfo) {
		this.orderResponseInfo = orderResponseInfo;
	}

}
