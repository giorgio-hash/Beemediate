package com.beemediate.beemediate.infrastructure.odoo.config;

import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import javax.security.auth.login.FailedLoginException;

import org.apache.xmlrpc.XmlRpcException;
import org.apache.xmlrpc.client.XmlRpcClient;
import org.apache.xmlrpc.client.XmlRpcClientConfigImpl;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.PropertySource;

/**
 * Classe di configurazione per comunicare con Odoo External API in protocollo XML-RPC. Le informazioni di configurazioni vengono prese dal file <i>src/main/resources/apiconfig.properties</i>.
 */
@Configuration
@PropertySource("classpath:apiconfig.properties")
public class OdooApiConfig {

	/***oggetto Logger*/
	private final Logger log = LoggerFactory.getLogger(OdooApiConfig.class);
	
	/**
	 * String che identifica il comando RPC per l'esecuzione di procedura remota
	 */
	public static final String EXECUTE_KW = "execute_kw";
	
	/**
	 * String che identifica il model dei contatti su model
	 */
	public static final String RES_PARTNER = "res.partner";
	
	/**
	 * String per l'header utile a specificare i campi di un model
	 */
	public static final String FIELDS = "fields";
	
	/**
	 * String che identifica l'operazione di lettura su model
	 */
	public static final String READ = "read";
	
	/**
	 * String che identifica l'operazione di scrittura su model
	 */
	public static final String WRITE = "write";
	
	/**
	 * String che identifica l'operazione di ricerca su model
	 */
	public static final String SEARCH = "search";
	
	/**
	 * String che identifica l'operazione di inserimento su model
	 */
	public static final String CREATE = "create";
	
	/**
	 * String con campo identificativo di un partner dal model
	 */
	public static final String PARTNER_ID_FIELD = "partner_id";
	/**
	 * Riferimento alla risorsa online CRM.
	 */
	private final String url;// scade 4.10
	/**
	 * Riferimento alla risorsa online database del CRM.
	 */
	private final String db; // scade 4.10
	/**
	 * Dato per l'autenticazione.
	 */
	private final String username;
	/**
	 * Token di autenticazione alle API Odoo.
	 */
	private final String password;// scade 23.09
	/**
	 * Serve a gestire il protocollo XML-RPC.
	 */
	private final XmlRpcClient client;
	/**
	 * Oggetto di comunicazione coi model via protocollo XML-RPC. Usa la configurazione objectConfig.
	 */
	private final XmlRpcClient models;
	/**
	 * Configurazione per informazioni di servizio dal server ed operazioni di autenticazione, via protocollo XML-RPC.
	 */
	private final XmlRpcClientConfigImpl commonConfig;
	/**
	 * Configurazione per interagire coi model di Odoo, via protocollo XML-RPC.
	 */
	private final XmlRpcClientConfigImpl objectConfig;
	/**
	 * Identificativo di sessione.
	 */
	private int uid;
	/**
	 * flag per segnalare stato della connessione.
	 */
	private boolean online = false;
	/**
	 * Stato degli Ordini a Fornitore, ovvero gli Ordini di Acquisto di Odoo.
	 */
	public enum OafStatus{
		NEW("NEW"),
		SHIPPED("SHIPPED"),
		CONFIRMED("CONFIRMED"),
		OPENTRANSERROR("OPENTRANSERROR"),
		CONTENTERROR("CONTENTERROR");
		
		/**
		 * String corrispondente allo stato
		 */
		public final String label;
		
		/**
		 * Costruttore privato
		 * @param label - String
		 */
		OafStatus(final String label) {
			this.label = label;
		}
		
		@Override
		public String toString() {
			return label;
		}
	}
	
	
	/**
	 * Costruttore usato da Spring per costruire la configurazione Odoo.
	 *
	 * I parametri annotati con @Value sono prelevati dal contesto delle proprietà "apiconfig.properties".
	 * gli argomenti XmlRpcClient e XmlRpcClientConfigImpl sono Spring bean
	 */
	@Autowired
	public OdooApiConfig (@Value("${api.host:noconf}") String url, @Value("${api.db:noconf}") String db, 
							@Value("${api.username:noconf}") String username, @Value("${api.key:noconf}") String password,
							@Qualifier("xmlRpcClientCommon") XmlRpcClient client, @Qualifier("xmlRpcClientModels") XmlRpcClient models,
							 @Qualifier("commonConfig") XmlRpcClientConfigImpl commonConfig, @Qualifier("objectConfig") XmlRpcClientConfigImpl objectConfig) {
		this.url = url;
		this.db = db;
		this.username = username;
		this.password = password;
		this.client = client;
		this.models = models;
		this.commonConfig = commonConfig;
		this.objectConfig = objectConfig;
	}
	
	
	/**
	 * Inizializza le configurazioni, verifica la connessione ed effettua autenticazione verso il CRM Odoo.
	 * @throws MalformedURLException
	 * @throws FailedLoginException
	 * @throws XmlRpcException
	 * @throws URISyntaxException 
	 */
	public void connect() throws MalformedURLException, FailedLoginException, XmlRpcException, URISyntaxException {
		
		//informazioni sul server
		commonConfig.setServerURL( (new URI(String.format("%s/xmlrpc/2/common", url))).toURL() );
		final Object ver = client.execute(commonConfig, "version", Collections.emptyList());
		
		//login
		try {
			uid = (int) client.execute(commonConfig, "authenticate", Arrays.asList(db, username, password, Collections.emptyMap()));

			log.info("Versione server: {}", ver.toString().replaceAll("[\r\n]","") );
			log.info("Session uid: {}", uid);
			
			//oggetto per interagire coi models di ODOO
			objectConfig.setServerURL( new URI(String.format("%s/xmlrpc/2/object", url)).toURL() );
			models.setConfig(objectConfig);
			
			online = true;
		
		} catch ( ClassCastException e ) {
			
			online = false;
			
			final FailedLoginException ex = new FailedLoginException("Eccezione durante il recupero uid di sessione, verificare il login.");
			ex.initCause(e);
			throw ex;
		}
	}
	
	
	/**
	 * 
	 * @return <i>true</i> se il servizio non ha riscontrato problemi di connessione con Odoo fino ad ora.
	 */
	public boolean isOnline() {
		return online;
	}
	
	
	/**
	 * Esegue una ricerca ("search") su un model Odoo tramite XML-RPC usando "execute_kw".
	 * Costruisce il payload con db/uid/password, il model, il metodo SEARCH e i parametri di ricerca.
	 *
	 * @param modelName  nome del model Odoo (es. "res.partner")
	 * @param details    kwargs opzionali (es. "fields", "limit", "order"); può essere null
	 * @param searchParams varargs di condizioni di ricerca (es. List.of(List.of("field","ilike","val")))
	 * @return           array di oggetti restituito dall'XML-RPC (castare in base al formato atteso)
	 * @throws XmlRpcException in caso di errori di comunicazione/risposta dal server Odoo
	 */
	public Object[] searchFromModel(String modelName, Map<String, Object> details, List<Object>... searchParams) throws XmlRpcException {
		return	remoteQueryOnModel(EXECUTE_KW,modelName,SEARCH,details,searchParams);
	}
	
	/**
	 * Esegue una lettura ("read") su un model Odoo delegando a remoteExcecuteOnModel.
	 *
	 * Invoca la procedure {@code execute_kw} sul servizio "models" per richiedere i record
	 * identificati da {@code ids}, applicando gli kwargs forniti in {@code details}.
	 *
	 * @param modelName nome del model Odoo (es. {@code "purchase.request"})
	 * @param details   mappa di kwargs opzionali (es. {@code "fields", "limit"}); può essere null
	 * @param ids       identificativi dei record da leggere (varargs); singoli id diventano {@code [[id1,id2,...]]}
	 * @return          array di oggetti restituito dall'XML-RPC (castare secondo il formato atteso)
	 * @throws XmlRpcException in caso di errori di comunicazione o risposta dal server Odoo
	 */
	public Object[] readFromModel(String modelName, Map<String, Object> details, Object... ids) throws XmlRpcException {
		
		return remoteQueryOnModel(EXECUTE_KW,modelName,READ,details,ids);
	}
	
	/**
	 * Esegue una scrittura ("write") su un model Odoo delegando alla chiamata remota generica.
	 *
	 * Invoca la procedure {@code execute_kw} sul model specificato per aggiornare il record
	 * identificato da {@code id} con i valori presenti in {@code details}.
	 *
	 * @param modelName nome del model Odoo (es. {@code "purchase.request"})
	 * @param details   mappa contenente i campi e i valori da aggiornare (es. {@code "field": value})
	 * @param id        identificativo del record da modificare
	 * @return          {@code true} se l'operazione ha avuto successo, altrimenti {@code false}
	 * @throws XmlRpcException in caso di errori nella chiamata XML-RPC
	 */
	public boolean updateOnModel(String modelName, Map<String, Object> details, Object id) throws XmlRpcException {
		
		return (boolean) models.execute(EXECUTE_KW,
											Arrays.asList(
													db,uid,password,
													modelName,WRITE,
													Arrays.asList(
															Arrays.asList(id),
															details
														))
											);
	}
	
	/**
	 * Inserisce un nuovo record su un model Odoo tramite XML-RPC e ritorna l'id creato.
	 *
	 * Invoca la procedure {@code execute_kw} (endpoint "models") con il metodo {@code create}
	 * per inserire i valori forniti in {@code details}. Nota: il model passato al payload
	 * è hardcoded a "mail.message" nel body della chiamata; se si vuole usare
	 * {@code modelName} sostituire opportunamente la stringa.
	 *
	 * @param modelName nome del model (non usato nell'attuale payload; attenzione al valore hardcoded)
	 * @param details   mappa dei campi e valori da inserire (es. {@code "subject": "...", "body": "..."})
	 * @return          identificativo intero del record creato restituito dal server Odoo
	 * @throws XmlRpcException in caso di errori di comunicazione o risposta dal server Odoo
	 */
	public int insertOnModel(String modelName, Map<String, Object> details) throws XmlRpcException {
		
		return (int) models.execute(EXECUTE_KW, 
						Arrays.asList(
						    db,uid,password,
						    modelName, CREATE,
						    Arrays.asList(details)
						    )
					    );
	}
	
	
	/**
	 * Esegue una chiamata XML-RPC in lettura su un model Odoo usando il procedure specificato.
	 *
	 * @param procedure nome della procedure XML-RPC (es. "execute_kw" o "execute")
	 * @param model     nome del model Odoo (es. "res.partner")
	 * @param operation metodo da invocare sul model (es. "read", "search", "write")
	 * @param details   mappa di kwargs opzionali per la chiamata (es. "fields", "limit"); può essere null
	 * @param params    parametri/argomenti varargs per l'operazione (es. condizioni di ricerca o id)
	 * @return          array di oggetti restituito dall'esecuzione XML-RPC (castare secondo il formato atteso)
	 * @throws XmlRpcException in caso di errori di comunicazione o risposta dal server Odoo
	 */
	private Object[] remoteQueryOnModel(String procedure, String model, String operation, Map<String,Object> details, Object... params) throws XmlRpcException {
		
		return (Object[]) models.execute(procedure,
				Arrays.asList(
						db,uid,password,
						model,	operation,
						Arrays.asList(Arrays.asList(params)),
						details
						)
				);
	}

	
}
