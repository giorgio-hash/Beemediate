package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

/**
 * Specifica i valori per degli attributi presenti nella struttura XML-OpenTrans
 */
public enum PartyType{
	SUPPLIER_SPECIFIC("supplier_specific"),BUYER_SPECIFIC("buyer_specific");
	
	/**
	 * String indicante il tipo di dato
	 */
	private final String type;
	
	/**
	 * Costruttore privato
	 * @param type - String 
	 */
	PartyType(final String type) {
		this.type = type;
	}
	
	@Override
	public String toString() {
		return type;
	}
}