package domain.core.ports.entrypoint;

import domain.core.dto.Confirmation;

public interface OrderConfirmedEventIF {

	//@ public model instance boolean newConfirmation;
	
	/*@ public normal_behaviour
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.orderID!=null & !\result.orderID.isEmpty();
	  @ ensures \typeof(\result) == \type(Confirmation);
	  @*/
	public /*@ pure @*/ Confirmation popConfirmation();
	
	/*@ public normal_behaviour
	  @ assigns newConfirmation;
	  @ ensures \result <==> newConfirmation; 
	  @*/
	public boolean hasConfirmation();
	
	/*@ public normal_behaviour
	  @ assigns newConfirmation;
	  @ ensures \result <==> newConfirmation; 
	  @*/
	public boolean fetchConfirmations();
	
}
