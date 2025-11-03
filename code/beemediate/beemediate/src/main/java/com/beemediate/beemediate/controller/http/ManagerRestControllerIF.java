package com.beemediate.beemediate.controller.http;

import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestMapping;

/***
 * Classe per input segnale verso il manager di servizio */

@RequestMapping(path = "/manage")
public interface ManagerRestControllerIF {

	/**
	 * API di contatto per verificare lo stato del servizio
	 * @return messaggio ReponseEntity con body String
	 */
    @GetMapping("/healthcheck")
    public ResponseEntity<String> checkHealth();
	
	/**API di contatto per attivare la procedura di rilevazione, validazione e caricamento degli ordini di acquisto pendenti su Odoo.
	 * */
    @GetMapping(path = "/orders")
    ResponseEntity manageOrders();
    
	/**API di contatto per attivare la procedura di rilevazione, archiviazione e notifica verso Odoo delle conferme agli ordini di acquisto.
	 * */
    @GetMapping(path = "/confirmations")
    ResponseEntity manageConfirmations();
}
