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

    @Bean
    public XmlRpcClientConfigImpl commonConfig() {
        return new XmlRpcClientConfigImpl();
    }

    @Bean
    public XmlRpcClientConfigImpl objectConfig() {
        return new XmlRpcClientConfigImpl();
    }

    @Bean
    public XmlRpcClient xmlRpcClientCommon() {
        return new XmlRpcClient();
    }

    @Bean
    public XmlRpcClient xmlRpcClientModels() {
        return new XmlRpcClient();
    }
}