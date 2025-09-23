package domain.core.ports.repository;

import domain.core.dto.Confirmation;

public interface HandleConfirmationIF {

	/*** Ritorna true se l'operazione è andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean archive(Confirmation c);
	
	/*** Ritorna true se l'operazione è andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean delete(Confirmation c);
	
}
