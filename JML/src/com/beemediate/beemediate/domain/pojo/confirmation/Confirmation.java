package com.beemediate.beemediate.domain.pojo.confirmation;

/***Classe per gestire la conferma ordine*/
public class Confirmation {
	
	/***struttura dati della conferma*/
	private /*@ spec_public @*/ final ConfirmationStructure data;
	
	/***identificativo dell'ordine di riferimento*/
	private /*@ spec_public @*/ final String confirmationId;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant confirmationId != null; @*/
	
	/**
	 * Costruttore
	 * @param d - Oggetto struttura dati conferma d'ordine
	 * @param cID - identificativo conferma d'ordine
	 */
	//@ requires d != null & cID!=null;
	//@ ensures data == d & confirmationId == cID;
	//@ pure
	public Confirmation(final String cID, final ConfirmationStructure d) {
		data = d;
		confirmationId = cID;
	}

	/**
	 * Restituisce copia della struttura dati della conferma d'ordine
	 * @return oggetto ConfirmationStructure
	 */
	/*@ public normal_behaviour
	  @ requires data != null; 
	  @ ensures \result != null;
	  @ ensures \result != data; 
	  @*/
	public ConfirmationStructure getData() {
		return new ConfirmationStructure(data);
	}
	
	/**
	 * Restituisce l'identificativo dell'ordine associato alla conferma
	 * @return oggetto String
	 */
	//@ ensures \result == confirmationId;
	public /*@ pure @*/ String getConfirmationId() {
		return confirmationId;
	}

}
