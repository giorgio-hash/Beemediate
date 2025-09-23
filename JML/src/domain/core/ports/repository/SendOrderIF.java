package domain.core.ports.repository;

import domain.core.dto.Order;

public interface SendOrderIF {

	/*** Ritorna true se l'operazione è andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires o!=null & o.data!=null & o.quantity!=null;
	  @ requires !o.hasOpenTransError(); 
	  @*/
	public /*@ pure */ boolean loadOrder(Order o);
	
}
