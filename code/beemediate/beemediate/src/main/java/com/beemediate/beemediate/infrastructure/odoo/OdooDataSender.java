package com.beemediate.beemediate.infrastructure.odoo;

import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import javax.security.auth.login.FailedLoginException;

import org.apache.xmlrpc.XmlRpcException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;
import com.beemediate.beemediate.infrastructure.ftp.exceptions.NullSuppliedArgumentException;
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;

/***Adattatore per comunicare con Odoo External API via protocollo XML-RPC. 
 * Riferirsi alla documentazione ufficiale di Odoo per ulteriori informazioni.*/
@Component
public class OdooDataSender implements DataSenderPort{

	/***logger di {@code Slf4j}*/
	private final Logger log = LoggerFactory.getLogger(OdooDataSender.class);
	/***Configurazione per comunicare con API del CRM Odoo.*/
	private final OdooApiConfig odoo;

	/**
	 * Messaggio di errore
	 */
	private static final String ERROR_MSG_ODOODB = "Problema nella scrittura del db Odoo.";
	
	/***
	 * Costruttore
	 * @param oggetto {@code OdooApiConfig}*/
	@Autowired
	public OdooDataSender(final OdooApiConfig odoo) {
		this.odoo = odoo;
	}
	
	
	@Override
	public boolean signalConfirmation(final Confirmation c) {
		
		try {
			return signal(c);
		} catch (FailedLoginException | MalformedURLException | XmlRpcException | URISyntaxException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		
		return false;
	}
	
	@Override
	public boolean signalShipped(final Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.SHIPPED.toString() );
		}catch(XmlRpcException | NullSuppliedArgumentException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		return res;
	}

	@Override
	public boolean signalOpenTransError(final Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.OPENTRANSERROR.toString() );
		}catch(XmlRpcException | NullSuppliedArgumentException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		return res;
	}

	@Override
	public boolean signalContentError(final  Order o) {

		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), OdooApiConfig
											.OafStatus
											.CONTENTERROR.toString() );
		}catch(XmlRpcException | NullSuppliedArgumentException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		return res;
	}
	
	
	
	//*******************************************//	
	//******** metodi helper di servizio ********//
	//*******************************************//
	
	private boolean signal(Confirmation c) throws FailedLoginException, MalformedURLException, XmlRpcException, URISyntaxException {
		
		// se non si è connessi, prova una connessione.
		if(!odoo.isOnline())
			odoo.connect();
		
		boolean res = false;
		ConfirmationStructure data = c.getData();
		String resourceID = c.getConfirmationId();
		try {
			res = updateTo(data.getOrderId(), OdooApiConfig
												.OafStatus
												.CONFIRMED.toString() );
			createWorkflowAnnotation(resourceID, data);
		}catch(XmlRpcException | InconsistentDTOException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}
	
	
	/**
	 * Aggiorna il model <tt>purchase.order</tt> di Odoo modificando il valore di <tt>x_studio_oaf</tt> dell'ordine di acquisto a <i>CONFIRMED, SHIPPED, OPENTRANSERROR, CONTENTERROR</i>. Per maggiori informazioni sui valori di <tt>x_studio_oaf</tt> vedi la classe enum {@code OafStatus } in {@code OdooApiConfig}.
	 * @param orderId - String per identificare ordine di acquisto nel sistema CRM
	 * @param oafState - String
	 * @return <i>true</i> se l'operazione è andata a buon fine
	 * @throws XmlRpcException per problemi legati alla applicazione del protocollo XML-RPC
	 */
	private boolean updateTo(final String orderId, final String oafState) throws XmlRpcException, NullSuppliedArgumentException {
		
		if(orderId==null || oafState==null)
			throw new NullSuppliedArgumentException ("Non sono ammessi argomenti null");
		
		Object[] ids;
		final Map<String, Object> requestInfo = new HashMap<>();
		
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
	
	
	
	private void createWorkflowAnnotation(String filename, ConfirmationStructure cs) throws XmlRpcException, InconsistentDTOException {
		
		Object[] ids;
		Object[] res;
		Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList("name","=",cs.getOrderId())
								)),
						requestInfo
						)
				);
		
		if (ids.length>1) throw new InconsistentDTOException("name ambiguo");
		if (ids.length==0) throw new InconsistentDTOException("name non trovato");
		
		//crea messaggio
		requestInfo.clear();
		requestInfo.put("model","purchase.order");
		requestInfo.put("res_id",ids[0]);
		requestInfo.put("message_type", "comment");
		requestInfo.put("body", writeConfirmationMessage(filename, cs));
		
		odoo.models.execute("execute_kw", 
				Arrays.asList(
				    odoo.getDb(), odoo.getUid(), odoo.getPassword(),
				    "mail.message", "create",
				    Arrays.asList(requestInfo)
				    )
			    );
	}
	
	
	private String writeConfirmationMessage(String filename, ConfirmationStructure cs) {
		return new StringBuilder()
				.append("ORDERRESPONSE")
				.append("<p>")
					.append("Archiviato il file ")
					.append(filename)
					.append(" con risposta all'ordine ")
					.append('\"').append(cs.getOrderId()).append('\"')
					.append('.')
				.append("</p>")
				.append("<ul>")
					.append("<li>").append("Data notifica: ")
										.append(cs.getOrderResponseDate())
										.append("</li>")
					.append("<li>").append("Data Consegna:")
										.append(cs.getDeliveryDate())
										.append("</li>")
					.append("<li>").append(cs.getTotalItemNum()).append(" articoli spediti a:")
											.append("<ul style=\"list-style-type:none;\">")
												.append("<li>").append(cs.getAddressName()).append("</li>")
												.append("<li>").append(cs.getAddressStreet()).append("</li>")
												.append("<li>").append(cs.getAddressCity())
																	.append(", ").append(cs.getAddressCountry())
																	.append('(').append(cs.getAddressCountryCoded()).append(')')
																	.append("</li>")
											.append("</ul>")
										.append("</li>")
					.append("<li>").append("Importo lordo: ")
										.append(cs.getTotalAmount()).append(' ')
										.append(cs.getCurrency())
										.append("</li>")
				.append("</ul>")
				.append("<p>Vedi file archiviato per altre informazioni.</p>")
				.toString();
	}
	
}
