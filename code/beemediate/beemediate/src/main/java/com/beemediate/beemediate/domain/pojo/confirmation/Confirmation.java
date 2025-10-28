package com.beemediate.beemediate.domain.pojo.confirmation;

/***Classe per gestire la conferma ordine*/
public class Confirmation {
	
	/***struttura dati della conferma*/
	private /*@ spec_public @*/ final ConfirmationStructure data;
	
	/***identificativo dell'ordine di riferimento*/
	private /*@ spec_public @*/ final String confirmationId;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant orderID != null; @*/
	
	/**
	 * Costruttore
	 * @param d - Oggetto struttura dati conferma d'ordine
	 * @param cID - identificativo conferma d'ordine
	 */
	//@ requires d != null & oID!=null;
	//@ ensures data == d & confirmationID == cID;
	//@ pure
	public Confirmation(final String cID, final ConfirmationStructure d) {
		data = d;
		confirmationId = cID;
	}

	/**
	 * Restituisce la copia della struttura dati della conferma d'ordine
	 * @return oggetto ConfirmationStructure
	 */
	//@ ensures \result != \old(data);
	public /*@ pure @*/ ConfirmationStructure getData() {
		return new ConfirmationStructure(data);
	}
	
	/**
	 * Restituisce l'identificativo dell'ordine associato alla conferma
	 * @return oggetto String
	 */
	//@ ensures \result == confirmationID;
	public /*@ pure @*/ String getConfirmationId() {
		return confirmationId;
	}

}
