package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

public class XmlPartyID{
	
	@JacksonXmlProperty(isAttribute=true)
	private String type = null;
	
	@JacksonXmlText
	private String partyId;
	
	public XmlPartyID(String partyId) {
		this.partyId = partyId;
	}
	
	public XmlPartyID(String partyId, PartyType partyType) {
		this.partyId = partyId;
		this.type = partyType.toString();
	}

	public String getType() {
		return type;
	}

	public String getPartyId() {
		return partyId;
	}
	
	
}