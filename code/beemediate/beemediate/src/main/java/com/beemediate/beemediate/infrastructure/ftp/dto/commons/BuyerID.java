package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Mappatura XML-OpenTrans con identificativi del prodotto dal sistema informativo del cliente
 */
@JacksonXmlRootElement(localName="bmecat:BUYER_PID")
public class BuyerID{
	
	/**
	 * identificativo prodotto nel sistema informativo del cliente
	 */
	@JacksonXmlText
	private String buyerId;
	
	/**
	 * Attributo conforme al formato XML-OpenTrans desiderato
	 */
	@JacksonXmlProperty(isAttribute=true)
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private String type;
	
	/**
	 * empty costructor for Jackson deserializer
	 */
	public BuyerID() {/*empty costructor for Jackson deserializer*/}
	
	/**
	 * Costruttore
	 * @param buyerId - String
	 */
	public BuyerID(String buyerId) {
		super();
		this.buyerId = buyerId;
	}
	
	/**
	 * Costruttore
	 * @param buyerId - String
	 */
	public BuyerID(String buyerId, String type) {
		super();
		this.buyerId = buyerId;
		this.type = type;
	}

	/**
	 * 
	 * @return String
	 */
	public String getBuyerId() {
		return buyerId;
	}

	/**
	 * 
	 * @return String
	 */
	public void setBuyerId(String buyerId) {
		this.buyerId = buyerId;
	}

	/**
	 * 
	 * @return String
	 */
	public String getType() {
		return type;
	}
	
}