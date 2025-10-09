package com.beemediate.beemediate.domain.exceptions;

/***Eccezione sollevata se contesti dove una certa soglia è irraggiungibile a priori*/
public class UnreachableThresholdException extends Exception {
	
	/**
	 * Costruttore
	 * @param msg - messaggio in testa all'eccezione quando verrà stampata su log
	 */
	/*@ public normal_behaviour
	  @ requires msg!=null;
	  @ ensures super.getMessage() == msg;
	  @ pure
	  @*/
	public UnreachableThresholdException(final String msg) {
		super(msg);
	}
}
