package com.beemediate.beemediate.domain.ports.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.Order;

public interface OrderProviderPort {
	
	//@ public model instance int newOrders;
	
	/*@ public invariant 0<=newOrders<=Integer.MAX_VALUE; @*/
	
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
	public Order popNewOrder();
	
	/*@ public normal_behaviour
	  @ ensures \result == newOrders>0; 
	  @*/
	public /*@ pure @*/ boolean hasNewOrder();
	
	/*@ public normal_behaviour
	  @ assigns newOrders;
	  @ ensures \result <==> newOrders > 0;   
	  @*/
	public boolean fetchOrders();

}