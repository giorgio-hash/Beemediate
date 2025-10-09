package com.beemediate.beemediate.domain.exceptions;

/***Eccezione sollevata in caso di array vuoto in un contesto dove ciò comprometterebbe l'esecuzione.*/
public class EmptyArrayException extends Exception {
	
	/**
	 * Costruttore
	 * @param msg - messaggio in testa all'eccezione quando verrà stampata su log
	 */
	/*@ public normal_behaviour
	  @ requires msg!=null;
	  @ ensures super.getMessage() == msg;
	  @ pure
	  @*/	
	public EmptyArrayException(final String msg) {
		super(msg);
	}
}
