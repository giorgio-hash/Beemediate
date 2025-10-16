package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

@JacksonXmlRootElement(localName = "PARTY")
public class XmlParty {
	
	@JacksonXmlProperty(localName="bmecat:PARTY_ID")
	private XmlPartyID partyId;
	@JacksonXmlProperty(localName="PARTY_ROLE")
	private String partyRole;
	
	public XmlParty(XmlPartyID partyId, String partyRole) {
		super();
		this.partyId = partyId;
		this.partyRole = partyRole;
	}
	
	public XmlPartyID getPartyId() {
		return partyId;
	}
	
	public String getPartyRole() {
		return partyRole;
	}
	
}
