package com.beemediate.beemediate.domain.pojo.confirmation;

/***Classe per gestire la conferma ordine*/
public class Confirmation {
	
	/***struttura dati della conferma*/
	private /*@ spec_public @*/ final Object data;
	
	/***identificativo dell'ordine di riferimento*/
	private /*@ spec_public @*/ final String orderID;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant orderID != null; @*/
	
	/**
	 * Costruttore
	 * @param d - Oggetto struttura dati conferma d'ordine
	 * @param oID - identificativo conferma d'ordine
	 */
	//@ requires d != null & oID!=null;
	//@ ensures data == d & orderID == oID;
	//@ pure
	public Confirmation(final Object d, final String oID) {
		data = d;
		orderID = oID;
	}

	/**
	 * Restituisce la struttura dati della conferma d'ordine
	 * @return oggetto Object
	 */
	//@ ensures \result == data;
	public /*@ pure @*/ Object getData() {
		return data;
	}
	
	/**
	 * Restituisce l'identificativo dell'ordine associato alla conferma
	 * @return oggetto String
	 */
	//@ ensures \result == orderID;
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

}
