package com.beemediate.beemediate.controller.http.impl;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.RestController;

import com.beemediate.beemediate.controller.http.ManagerRestControllerIF;
import com.beemediate.beemediate.domain.ports.controller.OaFManagerPort;

/**
 * Controller REST che implementa l'interfaccia ManagerRestControllerIF.
 * Funge da Adapter primario (in terminologia Hexagonal Architecture), esponendo
 * le funzionalità di gestione ordini e conferme via HTTP.
 */
@RestController
public class ManagerRestController implements ManagerRestControllerIF{

	/**
     * Logger SLF4J per il tracciamento delle operazioni e degli errori.
     */
	private final Logger log = LoggerFactory.getLogger(ManagerRestController.class);
	
	/**
	 * Gestore delle funzionalità core dell'applicativo
	 */
	private final OaFManagerPort oafManager;
	
	/**
     * Costruttore 
     * * @param oafManagerPort L'istanza del servizio di business.
     */
	@Autowired
	public ManagerRestController(final OaFManagerPort oafManagerPort) {
		this.oafManager = oafManagerPort;
	}

	/**
     * Endpoint di Health Check.
     * Utile per monitorare se il servizio è raggiungibile 
     */
	@Override
    public ResponseEntity<String> checkHealth() {
        return ResponseEntity.ok("Backend attiva");
    }
	
	/**
     * Endpoint per attivare l'elaborazione degli ordini.
     * Gestisce il flusso, logga il risultato e cattura eventuali eccezioni per evitare crash non gestiti.
     */
	@Override
	public ResponseEntity manageOrders() {
		try {
			final int processed = oafManager.handleOrders();
			log.info("manageOrders -> processed {} orders", processed);
			
			// Restituisco 200 con messaggio esplicito sul numero di elementi processati
			return ResponseEntity.ok("Processed " + processed + " orders.");
		} catch (Exception e) {
			// Log dell'errore e risposta 500 con messaggio diagnostico minimale
			log.error("manageOrders -> error while processing orders", e);
			return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
					.body("Error while processing orders");
		}
	}

	/**
     * Endpoint per attivare l'elaborazione delle conferme.
     * Struttura speculare a manageOrders.
     */
	@Override
	public ResponseEntity manageConfirmations() {
		try {
			final int processed = oafManager.handleConfirmations();
			log.info("manageConfirmations -> processed {} confirmations", processed);
			
			// Restituisco 200 con messaggio esplicito sul numero di elementi processati
			return ResponseEntity.ok("Processed " + processed + " confirmations.");
		} catch (Exception e) {
			log.error("manageConfirmations -> error while processing confirmations", e);
			return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
					.body("Error while processing confirmations");
		}
	}

}