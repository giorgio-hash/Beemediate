package com.beemediate.beemediate.infrastructure.odoo.exceptions;

/**
 * Segnala che il DTO non possiede i valori necessari a completare la procedura.
 */
public class InconsistentDTOException extends Exception {
	
	/**
	 * 
	 * @param message - String
	 */
	public InconsistentDTOException(final String message) {
		super(message);
	}

}
