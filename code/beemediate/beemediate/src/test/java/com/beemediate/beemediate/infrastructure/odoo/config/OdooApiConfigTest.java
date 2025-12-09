package com.beemediate.beemediate.infrastructure.odoo.config;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;

import javax.security.auth.login.FailedLoginException;

import org.apache.xmlrpc.XmlRpcException;
import org.apache.xmlrpc.client.XmlRpcClient;
import org.apache.xmlrpc.client.XmlRpcClientConfig;
import org.apache.xmlrpc.client.XmlRpcClientConfigImpl;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.mockito.Mock;
import org.mockito.junit.MockitoJUnitRunner;

@RunWith(MockitoJUnitRunner.class)
public class OdooApiConfigTest {

    @Mock
    private XmlRpcClient client;

    @Mock
    private XmlRpcClientConfigImpl commonConfig;

    @Mock
    private XmlRpcClientConfigImpl objectConfig;

    @Mock
    private XmlRpcClient models;

    private OdooApiConfig odoo;

    @Before
    public void setUp() {

        odoo = new OdooApiConfig(
                "http://localhost:8069",
                "mydb",
                "user",
                "pass",
                client,
                models,
                commonConfig,
                objectConfig
        );
    }

    @Test
    public void connect_success_setsOnlineTrue_andConfiguresModels() throws Exception {
        when(client.execute(any(XmlRpcClientConfig.class), eq("version"), anyList()))
                .thenReturn(Collections.singletonMap("server_version", "1.0"));
        when(client.execute(any(XmlRpcClientConfig.class), eq("authenticate"), anyList()))
                .thenReturn(42);

        odoo.connect();

        assertTrue(odoo.isOnline());
        verify(commonConfig, times(1)).setServerURL(any());
        verify(objectConfig, times(1)).setServerURL(any());
        verify(models, times(1)).setConfig(objectConfig);
    }

    @Test(expected = FailedLoginException.class)
    public void connect_whenAuthenticateReturnsWrongType_throwsFailedLoginException() throws Exception {
        when(client.execute(any(XmlRpcClientConfig.class), eq("version"), anyList()))
                .thenReturn(Collections.singletonMap("server_version", "1.0"));
        when(client.execute(any(XmlRpcClientConfig.class), eq("authenticate"), anyList()))
                .thenReturn("not-an-int");

        try {
            odoo.connect();
        } finally {
            assertFalse(odoo.isOnline());
        }
    }

    @Test(expected = XmlRpcException.class)
    public void connect_propagatesXmlRpcException_fromVersionCall() throws Exception {
        when(client.execute(any(XmlRpcClientConfig.class), eq("version"), anyList()))
                .thenThrow(new XmlRpcException("rpc failure"));

        odoo.connect();
    }

    @Test
    public void searchFromModel_delegates_andReturnsArray() throws Exception {
        Object[] expected = new Object[]{1, 2, 3};
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(expected);

        Object[] res = odoo.searchFromModel("res.partner", new HashMap<>(), Arrays.asList("name","=","X"));

        assertArrayEquals(expected, res);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

    @Test(expected = XmlRpcException.class)
    public void searchFromModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.searchFromModel("res.partner", null, Arrays.asList("x"));
    }

    @Test
    public void readFromModel_delegates_andReturnsArray() throws Exception {
        Object[] expected = new Object[]{ new HashMap<>() };
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(expected);

        Object[] res = odoo.readFromModel("purchase.order", Collections.singletonMap("fields", Arrays.asList("name")), 10);

        assertArrayEquals(expected, res);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

    @Test(expected = XmlRpcException.class)
    public void readFromModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.readFromModel("purchase.order", null, 1, 2, 3);
    }

    @Test
    public void updateOnModel_returnsBooleanFromModelsExecute() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(Boolean.TRUE);

        boolean ok = odoo.updateOnModel("purchase.order", Collections.singletonMap("x_studio_oaf","SHIPPED"), 55);

        assertTrue(ok);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

    @Test(expected = XmlRpcException.class)
    public void updateOnModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.updateOnModel("purchase.order", new HashMap<>(), 77);
    }

    @Test
    public void insertOnModel_returnsIntFromModelsExecute() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(987);

        int id = odoo.insertOnModel("mail.message", Collections.singletonMap("body","msg"));

        assertEquals(987, id);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

    @Test(expected = XmlRpcException.class)
    public void insertOnModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.insertOnModel("mail.message", new HashMap<>());
    }
    
}