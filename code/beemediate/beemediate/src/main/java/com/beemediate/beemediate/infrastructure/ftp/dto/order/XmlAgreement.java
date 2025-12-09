package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Ordini di contratto
 */
@JacksonXmlRootElement(localName="AGREEMENT")
public class XmlAgreement {
	/**
	 * Numero di contratto
	 */
	@JacksonXmlProperty(localName="bmecat:AGREEMENT_ID")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private String id;

	
	/**
	 * empty constructor for deserialization
	 */
	public XmlAgreement() {/*empty constructor for deserialization*/}
	
	/**
	 * Costruttore
	 * @param id
	 */
	public XmlAgreement(final String id) {
		this.id=id;
	}
	/**
	 * 
	 * @return
	 */
	public String getId() {
		return id;
	}

	/**
	 * 
	 * @param id
	 */
	public void setId(final String id) {
		this.id = id;
	}	
}