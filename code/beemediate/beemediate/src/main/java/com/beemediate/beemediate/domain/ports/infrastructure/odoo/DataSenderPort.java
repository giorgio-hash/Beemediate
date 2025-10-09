package com.beemediate.beemediate.domain.ports.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Port per gestire l'adattatore che manda informazioni verso il gestionale Odoo.
 */
public interface DataSenderPort {
	
	//@ public model instance boolean positiveResponse;
	
	/**
	 * Segnala al gestionale la conferma dell'ordine.
	 * @param c - Confirmation
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 */
	/*@ public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires c!=null;
	  @ requires !c.getOrderID().isEmpty();
	  @ ensures \result==positiveResponse;
	  @ also public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires (c!=null & c.getOrderID().isEmpty()) | c==null;
	  @ ensures !\result;
	  @*/
	/*@ spec_public @*/boolean signalConfirmation(Confirmation c);
	
	/**
	 * Segnala al gestionale la l'invio del Order.
	 * @param o - Order
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 */
	/*@ public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires o!=null;
	  @ requires !o.getOrderID().isEmpty();
	  @ ensures \result==positiveResponse;
	  @ also public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires (o!=null & o.getOrderID().isEmpty()) | o==null;
	  @ ensures !\result;
	  @*/
	/*@ spec_public @*/boolean signalShipped(Order o);
	
	/**
	 * Segnala al gestionale la presenza nel Order di errori OpenTransError.
	 * @param o - Order
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 */
	/*@ public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires o!=null;
	  @ requires !o.getOrderID().isEmpty();
	  @ ensures \result==positiveResponse;
	  @ also public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires (o!=null & o.getOrderID().isEmpty()) | o==null;
	  @ ensures !\result;
	  @*/
	/*@ spec_public @*/boolean signalOpenTransError(Order o);
	
	/**
	 * Segnala al gestionale la presenza nel Order di errori ContentError.
	 * @param o - Order
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 */
	/*@ public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires o!=null;
	  @ requires !o.getOrderID().isEmpty();
	  @ ensures \result==positiveResponse;
	  @ also public normal_behaviour
	  @ assigns positiveResponse;
	  @ requires (o!=null & o.getOrderID().isEmpty()) | o==null;
	  @ ensures !\result;
	  @*/
	/*@ spec_public @*/boolean signalContentError(Order o);

}
