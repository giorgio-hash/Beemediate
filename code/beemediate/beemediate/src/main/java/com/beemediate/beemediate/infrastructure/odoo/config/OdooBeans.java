package com.beemediate.beemediate.infrastructure.odoo.config;

import org.apache.xmlrpc.client.XmlRpcClient;
import org.apache.xmlrpc.client.XmlRpcClientConfigImpl;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;

/**
 * Spring configuration class that exposes XmlRpcClient and its configs as beans.
 * These beans can be injected (e.g. with @Autowired or @Inject) into classes that
 * need to perform XML-RPC calls to Odoo, improving testability and configurability.
 */
@Configuration
public class OdooBeans {

	/**
	 * @returns Bean di configurazione per informazioni di servizio dal server ed operazioni di autenticazione, via protocollo XML-RPC.
	 */
    @Bean
    public XmlRpcClientConfigImpl commonConfig() {
        return new XmlRpcClientConfigImpl();
    }

	/**
	 * @returns Bean di configurazione per interagire coi model di Odoo, via protocollo XML-RPC.
	 */
    @Bean
    public XmlRpcClientConfigImpl objectConfig() {
        return new XmlRpcClientConfigImpl();
    }

	/**
	 * @returns Bean di comunicazione a gestire il protocollo XML-RPC.
	 */
    @Bean
    public XmlRpcClient xmlRpcClientCommon() {
        return new XmlRpcClient();
    }
    
	/**
	 * @returns Bean di comunicazione coi model via protocollo XML-RPC. Usa la configurazione objectConfig.
	 */
    @Bean
    public XmlRpcClient xmlRpcClientModels() {
        return new XmlRpcClient();
    }
}