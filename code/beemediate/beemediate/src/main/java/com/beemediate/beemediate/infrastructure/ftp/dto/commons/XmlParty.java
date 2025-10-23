package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans con informazioni sul partner commerciale
 */
@JacksonXmlRootElement(localName = "PARTY")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
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
	 * tag per i dettagli di domicilio
	 */
	@JacksonXmlProperty(localName="ADDRESS")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlAddress address;
	
	/**
	 * Costruttore
	 * @param partyId - XmlPartyID
	 * @param partyRole - partyRole
	 */
	public XmlParty(final XmlPartyID partyId, final String partyRole) {
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

	/**
	 * 
	 * @return XmlAddress
	 */
	public XmlAddress getAddress() {
		return address;
	}
	
	
	/**
	 * @param XmlPartyID
	 */
	public void setPartyId(XmlPartyID partyId) {
		this.partyId = partyId;
	}

	/**
	 * 
	 * @param partyRole
	 */
	public void setPartyRole(String partyRole) {
		this.partyRole = partyRole;
	}

	/**
	 * 
	 * @param address
	 */
	public void setAddress(XmlAddress address) {
		this.address = address;
	}
	
	
	
}
