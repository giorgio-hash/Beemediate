package com.beemediate.beemediate.domain.ports.infrastructure.odoo.ftp;

import com.beemediate.beemediate.domain.pojo.order.Order;

public interface OrderSenderPort {

	/*** Ritorna true se l'operazione � andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires o!=null & o.data!=null & o.quantity!=null;
	  @ requires !o.hasOpenTransError(); 
	  @*/
	public /*@ pure */ boolean loadOrder(Order o);
	
}
