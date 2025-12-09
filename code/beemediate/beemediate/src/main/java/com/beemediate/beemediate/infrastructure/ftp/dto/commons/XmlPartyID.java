package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Tag per l'identificativo del partner commerciale
 */
public class XmlPartyID{
	
	/**
	 * Attributo conforme al formato XML-OpenTrans desiderato
	 */
	@JacksonXmlProperty(isAttribute=true)
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private String type;
	
	/**
	 * tag identificativo
	 */
	@JacksonXmlText
	private String partyId;
	
	/**
	 * Empty Constructor for Jackson deserializer
	 */
	public XmlPartyID() {/*Empty Constructor for Jackson deserializer*/}
	
	/**
	 * Costruttore
	 * @param partyId - String
	 */
	public XmlPartyID(final String partyId) {
		this.partyId = partyId;
	}

	/**
	 * Costruttore
	 * @param partyId - identiifcativo partner commerciale
	 * @param partyType - String che specifica il sistema di riferimento nel quale è registrato l'identificativo
	 */
	public XmlPartyID(final String partyId, final String partyType) {
		this.partyId = partyId;
		this.type = partyType;
	}
	
	/**
	 * Costruttore
	 * @param partyId - identiifcativo partner commerciale
	 * @param partyType - enum PartyType, specifica il sistema di riferimento nel quale è registrato l'identificativo
	 */
	public XmlPartyID(final String partyId, final PartyType partyType) {
		this.partyId = partyId;
		this.type = partyType.toString();
	}

	public String getType() {
		return type;
	}

	public void setType(final String type) {
		this.type = type;
	}

	public String getPartyId() {
		return partyId;
	}

	public void setPartyId(final String partyId) {
		this.partyId = partyId;
	}
	
}