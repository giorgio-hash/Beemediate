package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Mappatura XML-OpenTrans con informazioni sul partner commerciale
 */
@JacksonXmlRootElement(localName = "PARTY")
public class XmlParty {
	
	/**
	 * Riferimento a XmlPartyID
	 */
	@JacksonXmlProperty(localName="bmecat:PARTY_ID")
	private XmlPartyID partyId;
	
	/**
	 * tag per il ruolo del partner commerciale
	 */
	@JacksonXmlProperty(localName="PARTY_ROLE")
	private String partyRole;
	
	/**
	 * Costruttore
	 * @param partyId - XmlPartyID
	 * @param partyRole - partyRole
	 */
	public XmlParty(XmlPartyID partyId, String partyRole) {
		super();
		this.partyId = partyId;
		this.partyRole = partyRole;
	}
	
	/**
	 * 
	 * @return XmlPartyID
	 */
	public XmlPartyID getPartyId() {
		return partyId;
	}
	
	/**
	 * 
	 * @return String
	 */
	public String getPartyRole() {
		return partyRole;
	}
	
}
