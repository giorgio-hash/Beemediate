package com.beemediate.beemediate.infrastructure.odoo;

import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import javax.security.auth.login.FailedLoginException;

import org.apache.xmlrpc.XmlRpcException;
import org.owasp.encoder.Encode;
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
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig.OafStatus;
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

		try {
			return signal(o, OafStatus.SHIPPED);
		} catch (FailedLoginException | MalformedURLException | XmlRpcException | URISyntaxException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		
		return false;
	}

	@Override
	public boolean signalOpenTransError(final Order o) {

		try {
			return signal(o, OafStatus.OPENTRANSERROR);
		} catch (FailedLoginException | MalformedURLException | XmlRpcException | URISyntaxException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		
		return false;
	}

	@Override
	public boolean signalContentError(final  Order o) {

		try {
			return signal(o, OafStatus.CONTENTERROR);
		} catch (FailedLoginException | MalformedURLException | XmlRpcException | URISyntaxException e) {
			log.error(ERROR_MSG_ODOODB,e);
		}
		
		return false;
	}
	
	
	
	//*******************************************//	
	//******** metodi helper di servizio ********//
	//*******************************************//

	/**
	 * Segnala (invia) un aggiornamento di stato per un ordine al servizio Odoo.
	 *
	 * Se non è connesso al servizio Odoo, tenta una connessione chiamando {@code odoo.connect()}.
	 * Successivamente prova ad aggiornare lo stato dell'ordine nel database remoto tramite
	 * {@code updateTo(orderId, status)}. Se durante la scrittura verso Odoo si verifica una
	 * {@link org.apache.xmlrpc.XmlRpcException}, questa viene catturata e loggata e la
	 * funzione restituisce {@code false}.
	 *
	 * @param o l'ordine da aggiornare; non deve essere {@code null}
	 * @param status lo stato che si vuole impostare; non deve essere {@code null}
	 * @return {@code true} se l'aggiornamento è andato a buon fine, {@code false} altrimenti
	 *         (compreso il caso in cui si verifichi un {@link org.apache.xmlrpc.XmlRpcException}
	 *         durante la scrittura, che viene gestita internamente)
	 * @throws FailedLoginException se il tentativo di connessione a Odoo fallisce a causa di credenziali non valide
	 * @throws MalformedURLException se l'URL usato per connettersi a Odoo è malformato
	 * @throws XmlRpcException se altre chiamate non gestite internamente sollevano questa eccezione.
	 *         Nota: l'eventuale {@code XmlRpcException} generata da {@code updateTo(...)} è
	 *         catturata all'interno del metodo e non viene propagata.
	 * @throws URISyntaxException se l'URI usato per la connessione è invalido
	 */
	private boolean signal(Order o, OafStatus status) throws FailedLoginException, MalformedURLException, XmlRpcException, URISyntaxException {
		
		// se non si è connessi, prova una connessione.
		if(!odoo.isOnline())
			odoo.connect();
		
		boolean res = false;
		try {
			res = updateTo(o.getOrderID(), status.toString() );
		}catch(XmlRpcException e) {
			log.info("Problema nella scrittura del db Odoo.",e);
		}
		return res;
	}
	

	/**
	 * Segnala (invia) la conferma di un ordine al servizio Odoo e crea l'annotazione di workflow
	 * corrispondente.
	 *
	 * Il metodo verifica prima se esiste una connessione attiva verso Odoo e, in caso negativo,
	 * tenta di connettersi chiamando {@code odoo.connect()}. Recupera i dati dalla
	 * {@link Confirmation} fornita, usa {@code updateTo(orderId, status)} per aggiornare lo stato
	 * dell'ordine su Odoo impostandolo su {@code OafStatus.CONFIRMED} e, successivamente,
	 * crea una workflow annotation tramite {@code createWorkflowAnnotation(resourceID, data)}.
	 *
	 * Eventuali {@link org.apache.xmlrpc.XmlRpcException} o {@link InconsistentDTOException}
	 * sollevate durante la scrittura sul DB remoto (ad es. da {@code updateTo} o
	 * {@code createWorkflowAnnotation}) vengono catturate qui, loggate e non vengono propagate.
	 *
	 * @param c la conferma da processare (non deve essere {@code null}); da essa vengono letti
	 *          {@link ConfirmationStructure} e l'ID della risorsa. Il metodo si aspetta che
	 *          {@code c.getData()} e {@code c.getConfirmationId()} ritornino valori validi.
	 * @return {@code true} se l'aggiornamento dello stato su Odoo è andato a buon fine,
	 *         {@code false} in caso contrario (inclusi i casi in cui si verifica un'eccezione
	 *         gestita internamente e loggata)
	 * @throws FailedLoginException se il tentativo di connessione a Odoo fallisce a causa di credenziali non valide
	 * @throws MalformedURLException se l'URL usato per connettersi a Odoo è malformato
	 * @throws XmlRpcException se una chiamata di connessione/interazione con Odoo (es. {@code odoo.connect()})
	 *         solleva questa eccezione prima che venga eseguito l'aggiornamento; le XmlRpcException
	 *         sollevate da {@code updateTo(...)} o {@code createWorkflowAnnotation(...)} sono invece
	 *         catturate e non propagate.
	 * @throws URISyntaxException se l'URI usato per la connessione è invalido
	 */
	private boolean signal(Confirmation c) throws FailedLoginException, MalformedURLException, XmlRpcException, URISyntaxException {
		
		// se non si è connessi, prova una connessione.
		if(!odoo.isOnline())
			odoo.connect();
		
		boolean res = false;
		ConfirmationStructure data = c.getData();
		String resourceID = c.getConfirmationId();
		try {
			res = updateTo(data.getOrderId(), OafStatus
												.CONFIRMED
												.toString() );
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
								Arrays.asList("name","=",orderId)
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
	
	
	/**
	 * Crea un'annotazione di workflow (un messaggio) su Odoo associata all'ordine identificato
	 * da {@code cs.getOrderId()}.
	 *
	 * Il metodo esegue una ricerca su Odoo (model "purchase.order") usando come filtro
	 * {@code [["name","=", cs.getOrderId()]]} e richiede al massimo un risultato
	 * (requestInfo con "limit" = 1). Se non viene trovato alcun ordine o se è presente
	 * ambiguità sull'ordine trovato, viene sollevata un'eccezione di tipo
	 * {@link InconsistentDTOException}. Se la ricerca ha successo viene creato un nuovo
	 * record sul model "mail.message" con:
	 *  - model = "purchase.order"
	 *  - res_id = id dell'ordine trovato
	 *  - message_type = "comment"
	 *  - body = risultato di {@code writeConfirmationMessage(filename, cs)}
	 *
	 * Le chiamate remote ad Odoo vengono effettuate tramite {@code odoo.models.execute} e
	 * possono generare {@link org.apache.xmlrpc.XmlRpcException} che vengono propagate.
	 *
	 * @param filename nome (ID della risorsa/file) passato a {@code writeConfirmationMessage}
	 *                 e incluso nel corpo del messaggio; non deve essere {@code null}
	 * @param cs struttura di conferma da cui ricavare l'ordine e i dettagli del messaggio;
	 *           non deve essere {@code null} e ci si aspetta che {@code cs.getOrderId()}
	 *           ritorni un valore valido
	 * @throws XmlRpcException se una chiamata XML-RPC verso Odoo fallisce (search/create)
	 * @throws InconsistentDTOException se la ricerca dell'ordine non è univoca oppure non
	 *         ritorna alcun risultato (rispettivamente "name ambiguo" o "name non trovato")
	 */	
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
	
	/**
	 * Costruisce il corpo HTML del messaggio di conferma (workflow annotation) da inviare a Odoo.
	 *
	 * Il messaggio include un'intestazione fissa "ORDERRESPONSE", informazioni sul file
	 * archiviato, l'ID dell'ordine e una lista con data notifica, data di consegna,
	 * numero totale di articoli, indirizzo di spedizione e l'importo lordo con valuta.
	  *
	  * N.B.: Costruisce il corpo HTML del messaggio di conferma, escapando i valori forniti con
	  * OWASP Java Encoder per prevenire XSS e rottura del markup.
	  *
	 * @param filename il nome del file archiviato relativo alla conferma; non deve essere {@code null}
	 * @param cs la struttura di conferma contenente i campi usati per popolare il messaggio;
	 *           non deve essere {@code null}. Il metodo si aspetta che i metodi di accesso
	 *           (es. {@code getOrderId()}, {@code getDeliveryDate()}, ecc.) restituiscano valori validi.
	 * @return una {@link String} contenente il corpo del messaggio in formato HTML
	 */	
	private String writeConfirmationMessage(String filename, ConfirmationStructure cs) {
	    // Format/convert i valori (date/numero) a stringa prima di codificarli
	    String fn = Encode.forHtmlContent(filename == null ? "" : filename);
	    String orderId = Encode.forHtmlContent(cs.getOrderId());
	    String responseDate = Encode.forHtmlContent(String.valueOf(cs.getOrderResponseDate()));
	    String deliveryDate = Encode.forHtmlContent(String.valueOf(cs.getDeliveryDate()));
	    String totalItems = Encode.forHtmlContent(String.valueOf(cs.getTotalItemNum()));
	    String addrName = Encode.forHtmlContent(cs.getAddressName());
	    String addrStreet = Encode.forHtmlContent(cs.getAddressStreet());
	    String addrCity = Encode.forHtmlContent(cs.getAddressCity());
	    String addrCountry = Encode.forHtmlContent(cs.getAddressCountry());
	    String addrCountryCoded = Encode.forHtmlContent(cs.getAddressCountryCoded());
	    String totalAmount = Encode.forHtmlContent(String.valueOf(cs.getTotalAmount()));
	    String currency = Encode.forHtmlContent(cs.getCurrency());
		return new StringBuilder()
				.append("ORDERRESPONSE")
				.append("<p>")
					.append("Archiviato il file ")
					.append(fn)
					.append(" con risposta all'ordine ")
					.append('\"').append(orderId).append('\"')
					.append('.')
				.append("</p>")
				.append("<ul>")
					.append("<li>").append("Data notifica: ")
										.append(responseDate)
										.append("</li>")
					.append("<li>").append("Data Consegna:")
										.append(deliveryDate)
										.append("</li>")
					.append("<li>").append(totalItems).append(" articoli spediti a:")
											.append("<ul style=\"list-style-type:none;\">")
												.append("<li>").append(addrName).append("</li>")
												.append("<li>").append(addrStreet).append("</li>")
												.append("<li>").append(addrCity)
																	.append(", ").append(addrCountry)
																	.append('(').append(addrCountryCoded).append(')')
																	.append("</li>")
											.append("</ul>")
										.append("</li>")
					.append("<li>").append("Importo lordo: ")
										.append(totalAmount).append(' ')
										.append(currency)
										.append("</li>")
				.append("</ul>")
				.append("<p>Vedi file archiviato per altre informazioni.</p>")
				.toString();
	}
	
}
