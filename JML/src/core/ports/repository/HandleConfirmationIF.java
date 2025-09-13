package core.ports.repository;

import core.DTO.Confirmation;

public interface HandleConfirmationIF {

	/*** Ritorna true se l'operazione � andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean archive(Confirmation c);
	
	/*** Ritorna true se l'operazione � andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean delete(Confirmation c);
	
}
