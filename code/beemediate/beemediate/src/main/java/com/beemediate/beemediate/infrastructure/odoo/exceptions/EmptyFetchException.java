package com.beemediate.beemediate.infrastructure.odoo.exceptions;

/**
 * Segnala che è stata ricevuta una response nella comunicazione XML-RPC contenente XML vuoto.
 */
public class EmptyFetchException extends Exception{
	/**
	 * 
	 * @param message - String
	 */
	public EmptyFetchException (final String message) {
		super(message);
	}
}
