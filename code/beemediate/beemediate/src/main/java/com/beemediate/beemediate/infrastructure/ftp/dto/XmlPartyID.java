package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Tag per l'identificativo del partner commerciale, usato in PARTY
 */
public class XmlPartyID{
	
	/**
	 * Attributo conforme al formato XML-OpenTrans desiderato
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String type = null;
	
	/**
	 * tag identificativo
	 */
	@JacksonXmlText
	private String partyId;
	
	/**
	 * Costruttore
	 * @param partyId - identiifcativo partner commerciale
	 * @param partyType - enum PartyType, specifica il sistema di riferimento nel quale è registrato l'identificativo
	 */
	public XmlPartyID(String partyId, PartyType partyType) {
		this.partyId = partyId;
		this.type = partyType.toString();
	}

	/**
	 * 
	 * @return String
	 */
	public String getType() {
		return type;
	}

	/**
	 * 
	 * @return String
	 */
	public String getPartyId() {
		return partyId;
	}
	
	
}