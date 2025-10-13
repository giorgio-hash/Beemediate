package com.beemediate.beemediate.config.odoo;

import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.Collections;

import javax.security.auth.login.FailedLoginException;

import org.apache.xmlrpc.XmlRpcException;
import org.apache.xmlrpc.client.XmlRpcClient;
import org.apache.xmlrpc.client.XmlRpcClientConfigImpl;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Value;
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
	 * Riferimento alla risorsa online CRM.
	 */
	@Value("${api.host:noconf}")
	public String url;// scade 4.10
	/**
	 * Riferimento alla risorsa online database del CRM.
	 */
	@Value("${api.db:noconf}")
	public String db; // scade 4.10
	/**
	 * Dato per l'autenticazione.
	 */
	@Value("${api.username:noconf}")
	public String username;
	/**
	 * Token di autenticazione alle API Odoo.
	 */
	@Value("${api.key:noconf}")
	public String password;// scade 23.09
	/**
	 * Serve a gestire il protocollo XML-RPC.
	 */
	public final XmlRpcClient client = new XmlRpcClient();
	/**
	 * Configurazione per informazioni di servizio dal server ed operazioni di autenticazione, via protocollo XML-RPC.
	 */
	public final XmlRpcClientConfigImpl commmonConfig = new XmlRpcClientConfigImpl();
	/**
	 * Configurazione per interagire coi model di Odoo, via protocollo XML-RPC.
	 */
	public final XmlRpcClientConfigImpl objectConfig = new XmlRpcClientConfigImpl();
	/**
	 * Oggetto di comunicazione coi model via protocollo XML-RPC. Usa la configurazione objectConfig.
	 */
	public final XmlRpcClient models = new XmlRpcClient();
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
		
		public final String label;
		
		private OafStatus(String label) {
			this.label = label;
		}
		
		@Override
		public String toString() {
			return label;
		}
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
		commmonConfig.setServerURL( (new URI(String.format("%s/xmlrpc/2/common", url))).toURL() );
		Object ver = client.execute(commmonConfig, "version", Collections.emptyList());
		
		//login
		try {
			uid = (int) client.execute(commmonConfig, "authenticate", Arrays.asList(db, username, password, Collections.emptyMap()));

			log.info("Versione server: {}", ver);
			log.info("Session uid: {}", uid);
			
			//oggetto per interagire coi models di ODOO
			objectConfig.setServerURL( new URI(String.format("%s/xmlrpc/2/object", url)).toURL() );
			models.setConfig(objectConfig);
			
			online = true;
		
		} catch ( ClassCastException e ) {
			
			online = false;
			
			FailedLoginException ex = new FailedLoginException("Eccezione durante il recupero uid di sessione, verificare il login.");
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
	 * Restitusice l'identificativo di sessione.
	 * @return int - uid di sessione
	 */
	public int getUid() {
		return uid;
	}

	/**
	 * Restituisce il riferimento alla risorsa CRM online.
	 * @return String - un URL, indirizzo web 
	 */
	public String getUrl() {
		return url;
	}

	/**
	 * Restituicse il riferimento alla risorsa database del CRM online.
	 * @return String - un URL, indirizzo web
	 */
	public String getDb() {
		return db;
	}

	/**
	 * Restituisce il token di autenticazione alle API Odoo.
	 * @return String - password
	 */
	public String getPassword() {
		return password;
	}

	
}
