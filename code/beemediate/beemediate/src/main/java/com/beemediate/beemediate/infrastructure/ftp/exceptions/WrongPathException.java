package com.beemediate.beemediate.infrastructure.ftp.exceptions;

/**
 * Eccezione che segnala l'uso di un path che conduce ad una risorsa di formato errato, o non esistente
 */
public class WrongPathException  extends Exception{
	
	/**
	 * Costruttore
	 * @param message
	 */
	public WrongPathException(final String message) {
		super(message);
	}
}
