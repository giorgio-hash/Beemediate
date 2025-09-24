package com.beemediate.beemediate.infrastructure.odoo.config;

import java.net.MalformedURLException;

import java.net.URL;
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


@Configuration
@PropertySource("classpath:apiconfig.properties")
public class OdooApiConfig {

	
	private final Logger log = LoggerFactory.getLogger(OdooApiConfig.class);
	
	@Value("${api.host:noconf}")
	public String url;// scade 4.10
	@Value("${api.db:noconf}")
	public String db; // scade 4.10
	@Value("${api.username:noconf}")
	public String username;
	@Value("${api.key:noconf}")
	public String password;// scade 23.09
	
	public final XmlRpcClient client = new XmlRpcClient();
	public final XmlRpcClientConfigImpl common_config = new XmlRpcClientConfigImpl();
	public final XmlRpcClientConfigImpl object_config = new XmlRpcClientConfigImpl();
	public final XmlRpcClient models = new XmlRpcClient();
	
	private int uid;
	private boolean online = false;
	
	
	
	public void connect() throws MalformedURLException, FailedLoginException, XmlRpcException {
		
		//informazioni sul server
		common_config.setServerURL(new URL(String.format("%s/xmlrpc/2/common", url)));
		Object ver = client.execute(common_config, "version", Collections.emptyList());
		
		//login
		try {
			uid = (int) client.execute(common_config, "authenticate", Arrays.asList(db, username, password, Collections.emptyMap()));

			log.info("Versione server: "+ver);
			log.info("Session uid: "+uid);
			
			//oggetto per interagire coi models di ODOO
			object_config.setServerURL(new URL(String.format("%s/xmlrpc/2/object", url)));
			models.setConfig(object_config);
			
			online = true;
		
		} catch ( ClassCastException e ) {
			
			online = false;
			
			throw new FailedLoginException("Eccezione durante il recupero uid di sessione (ClassCastException), verificare il login. Eccezione: " + e.getMessage());
		}
	}
	
	
	public boolean isOnline() {
		return online;
	}

	public int getUid() {
		return uid;
	}


	public String getUrl() {
		return url;
	}


	public String getDb() {
		return db;
	}


	public String getPassword() {
		return password;
	}

	
}
