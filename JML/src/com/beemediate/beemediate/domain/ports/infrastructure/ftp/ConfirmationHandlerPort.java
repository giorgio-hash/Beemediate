package com.beemediate.beemediate.domain.ports.infrastructure.ftp;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;

public interface ConfirmationHandlerPort {

	/*** Ritorna true se l'operazione ? andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean archive(Confirmation c);
	
	/*** Ritorna true se l'operazione ? andata bene
	 * */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	public /*@ pure */ boolean delete(Confirmation c);
	
}
