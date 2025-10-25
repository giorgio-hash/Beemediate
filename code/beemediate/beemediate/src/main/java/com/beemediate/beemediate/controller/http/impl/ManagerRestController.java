package com.beemediate.beemediate.controller.http.impl;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.RestController;

import com.beemediate.beemediate.controller.http.ManagerRestControllerIF;
import com.beemediate.beemediate.domain.ports.controller.OaFManagerPort;

@RestController
public class ManagerRestController implements ManagerRestControllerIF{

	/***
	 * Riferimento all'istanza singleton LoggerFactory.*/
	private final Logger log = LoggerFactory.getLogger(ManagerRestController.class);
	
	/**
	 * Gestore delle funzionalità core dell'applicativo
	 */
	private final OaFManagerPort oafManager;
	
	@Autowired
	public ManagerRestController(OaFManagerPort oafManagerPort) {
		this.oafManager = oafManagerPort;
	}
	
	
	@Override
	public ResponseEntity manageOrders() {
		try {
			int processed = oafManager.handleOrders();
			log.info("manageOrders -> processed {} orders", processed);
			
			// Restituisco 200 con messaggio esplicito sul numero di elementi processati
			return ResponseEntity.ok("Processed " + processed + " orders.");
		} catch (Exception e) {
			// Log dell'errore e risposta 500 con messaggio diagnostico minimale
			log.error("manageOrders -> error while processing orders", e);
			return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
					.body("Error while processing orders: " + e.getMessage());
		}
	}

	@Override
	public ResponseEntity manageConfirmations() {
		try {
			int processed = oafManager.handleConfirmations();
			log.info("manageConfirmations -> processed {} confirmations", processed);
			if (processed > 0) {
				return ResponseEntity.ok("Processed " + processed + " confirmations.");
			} else {
				return ResponseEntity.noContent().build();
			}
		} catch (Exception e) {
			log.error("manageConfirmations -> error while processing confirmations", e);
			return ResponseEntity.status(HttpStatus.INTERNAL_SERVER_ERROR)
					.body("Error while processing confirmations: " + e.getMessage());
		}
	}

}