package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.PartyType;
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
	private final String type;
	
	/**
	 * tag identificativo
	 */
	@JacksonXmlText
	private final String partyId;
	
	/**
	 * Costruttore
	 * @param partyId - identiifcativo partner commerciale
	 * @param partyType - enum PartyType, specifica il sistema di riferimento nel quale è registrato l'identificativo
	 */
	public XmlPartyID(final String partyId, final PartyType partyType) {
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