package com.beemediate.beemediate.domain.ports.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.Order;

public interface OrderProviderPort {
	
	//@ public model instance boolean newOrder;
	
	/*@ public normal_behaviour
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.quantity!=null;
	  @ ensures \result.orderID!=null;
	  @ ensures \typeof(\result) == \type(Order);
	  @*/
	public /*@ pure @*/ Order popNewOrder();
	
	/*@ public normal_behaviour
	  @ assigns newOrder;
	  @ ensures \result <==> newOrder; 
	  @*/
	public boolean hasNewOrder();
	
	/*@ public normal_behaviour
	  @ assigns newOrder;
	  @ ensures \result <==> newOrder; 
	  @*/
	public boolean fetchOrders();

}