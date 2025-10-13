package com.beemediate.beemediate.infrastructure.odoo;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import org.apache.xmlrpc.XmlRpcException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.config.odoo.OdooApiConfig;
import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;

/***Adattatore per comunicare con Odoo External API via protocollo XML-RPC. 
 * Riferirsi alla documentazione ufficiale di Odoo per ulteriori informazioni.*/
@Component
public class OdooDataSender implements DataSenderPort{

	/***logger di {@code Slf4j}*/
	private final Logger log = LoggerFactory.getLogger(OdooDataSender.class);
	/***Configurazione per comunicare con API del CRM Odoo.*/
	private final OdooApiConfig odoo;

	/***
	 * Costruttore
	 * @param oggetto {@code OdooApiConfig}*/
	@Autowired
	public OdooDataSender(final OdooApiConfig odoo) {
		this.odoo = odoo;
	}
	
	
	@Override
	public boolean signalConfirmation(Confirmation c) {
		
		boolean res = false;
		try {
			res = updateTo(c.getOrderID(), OdooApiConfig
											.OafStatus
											.CONFIRMED.toString() );
		}catch(XmlRpcException | NullPointerException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}
	
	@Override
	public boolean signalShipped(Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.SHIPPED.toString() );
		}catch(XmlRpcException | NullPointerException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}

	@Override
	public boolean signalOpenTransError(Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.OPENTRANSERROR.toString() );
		}catch(XmlRpcException | NullPointerException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}

	@Override
	public boolean signalContentError(Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.CONTENTERROR.toString() );
		}catch(XmlRpcException | NullPointerException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}
	
	
	
	//*******************************************//	
	//******** metodi helper di servizio ********//
	//*******************************************//
	
	
	/**
	 * Aggiorna il model <tt>purchase.order</tt> di Odoo modificando il valore di <tt>x_studio_oaf</tt> dell'ordine di acquisto a <i>CONFIRMED, SHIPPED, OPENTRANSERROR, CONTENTERROR</i>. Per maggiori informazioni sui valori di <tt>x_studio_oaf</tt> vedi la classe enum {@code OafStatus } in {@code OdooApiConfig}.
	 * @param orderId - String per identificare ordine di acquisto nel sistema CRM
	 * @param oafState - String
	 * @return <i>true</i> se l'operazione è andata a buon fine
	 * @throws XmlRpcException per problemi legati alla applicazione del protocollo XML-RPC
	 */
	private boolean updateTo(String orderId, String oafState) throws XmlRpcException {
		
		if(orderId==null || oafState==null)
			throw new NullPointerException ("Non sono ammessi argomenti null");
		
		Object[] ids = null;
		Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList("origin","=",orderId)
								)),
						requestInfo
						)
				);
		
		requestInfo.clear();		
		requestInfo.put("x_studio_oaf", oafState );
		
		return (boolean) odoo.models.execute("execute_kw", 
						Arrays.asList(
						    odoo.getDb(), odoo.getUid(), odoo.getPassword(),
						    "purchase.order", "write",
						    Arrays.asList(Arrays.asList(ids[0]),
						    requestInfo
						    )
					    )
					);
		
	}
	
}
