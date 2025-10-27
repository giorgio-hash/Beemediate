package com.beemediate.beemediate.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.*;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.dto.*;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.*;
import com.beemediate.beemediate.infrastructure.odoo.mapper.OrderMapper;

import org.apache.xmlrpc.XmlRpcException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.security.auth.login.FailedLoginException;

/**
 * Adattatore che implementa OrderProviderPort. Recupera gli ordini di acquisto dal CRM Odoo, ricostruisce i corrispondenti Order e li conserva in un buffer.
 */
@Component
public class OdooOrderProvider implements OrderProviderPort{
	
	/**
	 * Buffer con singolo elemento Order.
	 */
	private Order ordine = null;
	
	/***riferimento a Logger*/
	private final Logger log = LoggerFactory.getLogger(OdooOrderProvider.class);
	/***Riferimento a Configurazione per autenticazione e comunicazione con CRM Odoo usando il protocollo XML-RPC.*/
	private final OdooApiConfig odoo;
	
	
	/**
	 * Costruttore
	 * @param odoo - configurazione per autenticazione e comunicazione con Odoo via XML-RPC
	 */
	@Autowired
	public OdooOrderProvider(final OdooApiConfig odoo) {
		this.odoo = odoo;
	}


	
	@Override
	public Order popNewOrder() {
		final Order o = ordine;
		ordine = null;
		return o;
	}



	@Override
	public boolean hasNewOrder() {
		return ordine != null;
	}



	@Override
	public boolean fetchOrders() {
		 
		ordine = null;
		
		try {
			return fetchData();
		}catch(MalformedURLException | FailedLoginException | XmlRpcException | URISyntaxException e){
			log.error("Problema nel recupero degli ordini.",e);
		}
		
		return false;
	}
	
	
	//*******************************************//	
	//******** metodi helper di servizio ********//
	//*******************************************//
	
	
	/**
	 * Richiede via XML-RPC le informazioni dei model di Odoo e ricostruisce l'oggetto Order.
	 * @return <i>true</i> se viene creato un nuovo Order.
	 * @throws MalformedURLException
	 * @throws FailedLoginException
	 * @throws XmlRpcException
	 * @throws URISyntaxException 
	 */
	private boolean fetchData() throws FailedLoginException, XmlRpcException, URISyntaxException, MalformedURLException {
		
		// se non si è connessi, prova una connessione.
		if(!odoo.isOnline())
			odoo.connect();
		
		
		ordine = null;
		
		try {
			
			final FornitoreDTO f;
			final PreventivoDTO prev;
			final ArticoloPreventivoDTO[] artpr;
			final ProdottoFornitoreDTO[] prodf;
			final DestinazioneDTO dest;
			final CompagniaDTO comp;
			final OrderStructure ordstr;
			
			
			//trova ed estrai GEALAN (e stampa su log)
			f = FornitoreDTO.fromXMLRPC(odoo);
			log.info(f.toString().toString().replaceAll("[\r\n]",""));
			
			
			//trova ed estrai preventivo (e stampa su log)
			prev = PreventivoDTO.fromXMLRPC(odoo, f);
			log.info(prev.toString().toString().replaceAll("[\r\n]",""));
			
			
			//trova informazioni sulla delivery specificata nel preventivo (e stampa su log)
			dest = DestinazioneDTO.fromXMLRPC(
							odoo,
							ContattoConsegnaDTO.fromXMLRPC(
										odoo,
										ConsegnaDTO.fromXMLRPC(odoo, prev)
									)
							);
			log.info(dest.toString().toString().replaceAll("[\r\n]",""));
			
			//trova informazioni sulla compagnia cliente (e stampa su log)
			comp = CompagniaDTO.fromXMLRPC(odoo, prev);
			log.info(comp.toString().toString().replaceAll("[\r\n]",""));
			
			//trova ed estrai parti del preventivo (e stampa su log)
			artpr = ArticoloPreventivoDTO.fromXMLRPC(odoo, prev);
			for(ArticoloPreventivoDTO p : artpr) {
				log.info(p.toString().toString().replaceAll("[\r\n]",""));
			}
			
			//per ogni prodotto associato ad una parte del preventivo, trova ed estrai info su catalogo fornitore (e stampa su log)
			prodf = ProdottoFornitoreDTO.fromXMLRPC(
								odoo,
								ProdottoDTO.fromXMLRPC(odoo, artpr),
								f
							);
			for(ProdottoFornitoreDTO p : prodf) {
				log.info(p.toString().toString().replaceAll("[\r\n]",""));
			}
			
			//costruzione struct ordine
			ordstr=OrderMapper.map(f, prev, artpr, prodf, dest, comp);
			log.info(ordstr.toString().toString().replaceAll("[\r\n]",""));
			//costruzione ordine
			ordine = new Order(ordstr, ordstr.getHeader().getOrderID() );
			
			
		} catch (InconsistentDTOException | ClassCastException e1) {
			log.error("Problema nel recupero degli ordini.",e1);
		} catch(EmptyFetchException e) {
			log.info("Problema nel recupero degli ordini: {}",e.getMessage());
		}
		
		return hasNewOrder();
		
	}


}
