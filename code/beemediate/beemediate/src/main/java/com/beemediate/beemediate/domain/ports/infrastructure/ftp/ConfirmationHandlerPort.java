package com.beemediate.beemediate.domain.ports.infrastructure.ftp;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;

/**
 * Port per gestire l'adattatore che manipola le conferme.
 */
@SuppressWarnings("PMD.ImplicitFunctionalInterface")
public interface ConfirmationHandlerPort {

	/**
	 * Esegue l'archiviazione della conferma sul sistema FTP.
	 * @param c - oggetto Confirmation
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 */
	/*@ public normal_behaviour 
	  @ requires c!=null & c.data!=null; 
	  @*/
	/*@ spec_public pure */ boolean archive(Confirmation c);
	
}
