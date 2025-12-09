package com.beemediate.beemediate.domain.ports.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Port per gestire l'adattatore incaricato di ricevere Order dal gestionale Odoo.
 * Si presume che l'adattatore segue un comportamento simile allo Stack.
 */
public interface OrderProviderPort {
	
	//@ public model instance int newOrders;
	
	/*@ public invariant 0<=newOrders<=Integer.MAX_VALUE; @*/
	
	/**
	 * Restituisce un nuovo Order
	 * @return Order
	 */
	/*@ public normal_behaviour
	  @ assigns newOrders;
	  @ requires newOrders>0;
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.quantity!=null;
	  @ ensures \result.orderID!=null;
	  @ ensures \typeof(\result) == \type(Order);
	  @ ensures newOrders == \old(newOrders)-1;
	  @
	  @ also public normal_behaviour
	  @ assigns \nothing;
	  @ requires newOrders==0;
	  @ ensures \result==null;
	  @*/
	Order popNewOrder();
	
	/**
	 * Determina se è ancora presente un Order
	 * @return Order
	 */
	/*@ public normal_behaviour
	  @ ensures \result == newOrders>0; 
	  @*/
	/*@ pure @*/ boolean hasNewOrder();
	
	/**
	 * Recupera nuovi Ordder
	 * @return Order
	 */
	/*@ public normal_behaviour
	  @ assigns newOrders;
	  @ ensures \result <==> newOrders > 0;   
	  @*/
	boolean fetchOrders();

}