package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

/**
 * Specifica il tipo di DeliveryDate
 */
public enum DeliveryDateType{
	OPTIONAL("optional"),FIXED("fixed");
	
	/**
	 * valore String
	 */
	private final String type;
	
	/**
	 * Costruttore private
	 * @param type - valore String corrispondente
	 */
	DeliveryDateType(String type){
		this.type=type;
	}
	
	@Override
	public String toString() {
		return type;
	}
}