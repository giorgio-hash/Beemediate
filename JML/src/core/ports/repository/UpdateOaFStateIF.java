package core.ports.repository;

import core.DTO.Confirmation;
import core.DTO.Order;


public interface UpdateOaFStateIF {
	
	//@ public model instance boolean positiveResponse;
	
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
	public boolean signalConfirmation(Confirmation c);
	
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
	public boolean signalShipped(Order o);
	
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
	public boolean signalOpenTransError(Order o);
	
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
	public boolean signalContentError(Order o);

}
