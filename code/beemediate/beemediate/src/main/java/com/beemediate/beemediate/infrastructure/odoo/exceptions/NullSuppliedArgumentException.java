package com.beemediate.beemediate.infrastructure.odoo.exceptions;

/**
 * Segnala che è stato fornito un input object con riferimento a <i>null</i> in un contesto dove non è consentito
 */
public class NullSuppliedArgumentException extends Exception{

	/**
	 * 
	 * @param message - String
	 */
	public NullSuppliedArgumentException(final String message) {
		super(message);
	}
}
