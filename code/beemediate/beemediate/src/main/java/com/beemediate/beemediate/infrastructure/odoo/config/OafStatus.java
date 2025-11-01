package com.beemediate.beemediate.infrastructure.odoo.config;
/**
 * Stato degli Ordini a Fornitore, ovvero gli Ordini di Acquisto di Odoo.
 */
public enum OafStatus{
	NEW("NEW"),
	SHIPPED("SHIPPED"),
	CONFIRMED("CONFIRMED"),
	OPENTRANSERROR("OPENTRANSERROR"),
	CONTENTERROR("CONTENTERROR");
	
	/**
	 * String corrispondente allo stato
	 */
	public final String label;
	
	/**
	 * Costruttore privato
	 * @param label - String
	 */
	OafStatus(final String label) {
		this.label = label;
	}
	
	@Override
	public String toString() {
		return label;
	}
}