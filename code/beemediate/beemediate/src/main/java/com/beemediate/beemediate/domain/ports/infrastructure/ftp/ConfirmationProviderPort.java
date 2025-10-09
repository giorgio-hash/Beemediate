package com.beemediate.beemediate.domain.ports.infrastructure.ftp;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;

/**
 * Port per gestire l'adattatore che restituisce le conferme.
 * Si presume che l'adattatore segue un comportamento simile allo Stack.
 */
public interface ConfirmationProviderPort {

	//@ public model instance boolean newConfirmation;
	
	/**
	 * L'adattatore ha un buffer con oggetti Confirmation. Con questo metodo, si può richiedere un oggetto Confirmation all'adattatore.
	 * @return oggetto Confirmation se disponibile, altrimenti <i>null</i>
	 */
	/*@ public normal_behaviour
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.orderID!=null & !\result.orderID.isEmpty();
	  @ ensures \typeof(\result) == \type(Confirmation);
	  @*/
	/*@ spec_public pure @*/ Confirmation popConfirmation();
	
	/**
	 * L'adattatore ha un buffer con oggetti Confirmation.
	 * @return <i>true</i> se il buffer dell'adattatore contiene almeno un Confirmation
	 */
	/*@ public normal_behaviour
	  @ assigns newConfirmation;
	  @ ensures \result <==> newConfirmation; 
	  @*/
	/*@ spec_public @*/boolean hasConfirmation();
	
	/**
	 * L'adattatore svuota il buffer, recupera gli oggetti Confirmation e riempie il buffer.
	 * @return <i>true</i> se il buffer è stato ripopolato con successo
	 */
	/*@ public normal_behaviour
	  @ assigns newConfirmation;
	  @ ensures \result <==> newConfirmation; 
	  @*/
	/*@ spec_public @*/boolean fetchConfirmations();
	
}
