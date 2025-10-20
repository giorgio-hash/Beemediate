package com.beemediate.beemediate.infrastructure.ftp.exceptions;

/**
 * Segnala che è stato fornito un input object con riferimento a <i>null</i> in un contesto dove non è consentito
 */
public class NullSuppliedArgumentException extends NullPointerException {

	/**
	 * 
	 * @param message - String
	 */
	public NullSuppliedArgumentException(final String message) {
		super(message);
	}
}
