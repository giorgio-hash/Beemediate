package com.beemediate.beemediate.domain.ports.entrypoint;

/**
 * Interfaccia per controllare le operazioni fondamentali della piattaforma.
 */
public interface OaFManagerPort {
	
	/**
	 * Verifica la presenza di conferme d'ordine e, se presenti, le processa.
	 * @return int - numero di conferme d'ordine effettivamente processate.
	 */
	int handleConfirmations();
	
	/**
	 * Verifica la presenza di ordini e, se presenti, procede a processarli.
	 * @return int - numero di ordini effettivamente processati.
	 */
	int handleOrders();

}
