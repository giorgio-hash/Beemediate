package com.beemediate.beemediate.domain.ports.infrastructure.ftp;

import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Port per gestire l'adattatore incaricato della spedizione di Order verso il fornitore.
 */
public interface OrderSenderPort {

	/**
	 * Carica Order sul FTP.
	 * @param o - Order
	 * @return <i>true</i> se l'operazione è stata completata con successo.
	 * 
	 */
	/*@ public normal_behaviour 
	  @ requires o!=null & o.data!=null & o.quantity!=null;
	  @ requires !o.hasOpenTransError(); 
	  @*/
	/*@ spec_public pure */ boolean loadOrder(final Order o);
	
}
