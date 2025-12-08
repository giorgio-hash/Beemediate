package com.beemediate.beemediate.domain.ports.infrastructure.ftp;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;

public interface ConfirmationProviderPort {

	//@ public model instance boolean newConfirmation;
	
	/*@ public normal_behaviour
	  @ ensures \result!=null;
	  @ ensures \result.data!=null;
	  @ ensures \result.confirmationId!=null & !\result.confirmationId.isEmpty();
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
