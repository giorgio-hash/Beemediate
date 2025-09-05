package entrypoint;

import DTO.Order;

public interface NewOrdersEventIF {
	
	//@ ensures \result != null & (\forall int i; 0<=i<=\result.length; \typeof(\result[i])==\type(Order));
	public /*@ pure @*/ Order[] fetchIncomingOrders ();

}
