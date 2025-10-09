package com.beemediate.beemediate.domain.ports.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Port per gestire l'adattatore incaricato di ricevere Order dal gestionale Odoo.
 * Si presume che l'adattatore segue un comportamento simile allo Stack.
 */
public interface OrderProviderPort {
	
	//@ public model instance boolean newOrder;
	
	/**
	 * L'adattatore ha un buffer con oggetti Order. Con questo metodo, si può richiedere un oggetto Order all'adattatore.
	 * @return oggetto Order se disponibile, altrimenti <i>null</i>
	 */
	/*@ public normal_behaviour
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.quantity!=null;
	  @ ensures \result.orderID!=null;
	  @ ensures \typeof(\result) == \type(Order);
	  @*/
	/*@ spec_public pure @*/ Order popNewOrder();
	
	/**
	 * L'adattatore ha un buffer con oggetti Order.
	 * @return <i>true</i> se il buffer dell'adattatore contiene almeno un Order
	 */
	/*@ public normal_behaviour
	  @ assigns newOrder;
	  @ ensures \result <==> newOrder; 
	  @*/
	/*@ spec_public @*/ boolean hasNewOrder();
	
	/**
	 * L'adattatore svuota il buffer, recupera gli oggetti Order e riempie il buffer.
	 * @return <i>true</i> se il buffer è stato ripopolato con successo
	 */
	/*@ public normal_behaviour
	  @ assigns newOrder;
	  @ ensures \result <==> newOrder; 
	  @*/
	/*@ spec_public @*/ boolean fetchOrders();

}