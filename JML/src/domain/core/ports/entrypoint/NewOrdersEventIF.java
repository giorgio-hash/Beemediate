package domain.core.ports.entrypoint;

import domain.core.dto.Order;

public interface NewOrdersEventIF {
	
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