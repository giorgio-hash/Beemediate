package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * caratteristica distintiva dell'oggetto di riferimento
 */
@JacksonXmlRootElement(localName="REMARKS")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlRemarks{
	
	/**
	 * tipo
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String type;

	/**
	 * testo
	 */
	@JacksonXmlText
	private String remarks;

	/**
	 * 
	 * @return String
	 */
	public String getType() {
		return type;
	}

	/**
	 * 
	 * @param type String
	 */
	public void setType(String type) {
		this.type = type;
	}

	/**
	 * 
	 * @return String
	 */
	public String getRemarks() {
		return remarks;
	}

	/**
	 * 
	 * @param remarks - String
	 */
	public void setRemarks(String remarks) {
		this.remarks = remarks;
	}

	
}