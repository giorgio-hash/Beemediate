package com.beemediate.beemediate.infrastructure.ftp.dto;

public enum PartyType{
	SUPPLIER_SPECIFIC("supplier_specific"),BUYER_SPECIFIC("buyer_specific");
	
	private final String type;
	
	private PartyType(String type) {
		this.type = type;
	}
	
	@Override
	public String toString() {
		return type;
	}
}