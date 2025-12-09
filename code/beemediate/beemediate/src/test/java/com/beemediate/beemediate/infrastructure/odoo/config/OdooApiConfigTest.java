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
import org.mockito.Mockito;
import org.mockito.junit.MockitoJUnitRunner;

/**
 * Test unitario per la classe di configurazione e comunicazione {@link OdooApiConfig}.
 * <p>
 * Verifica la corretta gestione del ciclo di vita della connessione XML-RPC verso Odoo
 * e la delega delle operazioni CRUD (search, read, update, insert) al client sottostante.
 * Utilizza {@link Mockito} per simulare le risposte del server Odoo ({@link XmlRpcClient})
 * ed evitare chiamate di rete reali.
 */
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

/**
     * Inizializza l'istanza di {@link OdooApiConfig} iniettando i mock delle dipendenze XML-RPC.
     * Questo permette di controllare completamente l'output delle chiamate remote simulate.
     */
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

/**
     * Verifica il successo della procedura di connessione e autenticazione.
     * <p>
     * Scenario:
     * <ul>
     * <li>La chiamata "version" ritorna correttamente.</li>
     * <li>La chiamata "authenticate" ritorna un ID utente valido (intero).</li>
     * </ul>
     * Risultato:
     * <ul>
     * <li>Lo stato {@code isOnline()} diventa {@code true}.</li>
     * <li>Vengono configurati gli URL dei client per le chiamate successive.</li>
     * </ul>
     */
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

/**
     * Verifica la gestione di una risposta di autenticazione non valida (es. credenziali errate).
     * <p>
     * Se Odoo ritorna un valore non intero (spesso `Boolean.FALSE` in caso di errore) durante
     * l'autenticazione, il metodo deve sollevare {@link FailedLoginException}.
     */
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

/**
     * Verifica che le eccezioni di rete (XmlRpcException) durante la connessione vengano propagate.
     */
    @Test(expected = XmlRpcException.class)
    public void connect_propagatesXmlRpcException_fromVersionCall() throws Exception {
        when(client.execute(any(XmlRpcClientConfig.class), eq("version"), anyList()))
                .thenThrow(new XmlRpcException("rpc failure"));

        odoo.connect();
    }

/**
     * Verifica che il metodo di ricerca {@code searchFromModel} deleghi correttamente al client XML-RPC
     * e restituisca l'array di ID trovato.
     */
    @Test
    public void searchFromModel_delegates_andReturnsArray() throws Exception {
        Object[] expected = new Object[]{1, 2, 3};
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(expected);

        Object[] res = odoo.searchFromModel("res.partner", new HashMap<>(), Arrays.asList("name","=","X"));

        assertArrayEquals(expected, res);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

/**
     * Verifica la propagazione delle eccezioni durante la ricerca.
     */
    @Test(expected = XmlRpcException.class)
    public void searchFromModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.searchFromModel("res.partner", null, Arrays.asList("x"));
    }

/**
     * Verifica che il metodo di lettura {@code readFromModel} deleghi correttamente al client XML-RPC
     * e restituisca l'array di record (Mappe/Dizionari) trovato.
     */
    @Test
    public void readFromModel_delegates_andReturnsArray() throws Exception {
        Object[] expected = new Object[]{ new HashMap<>() };
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(expected);

        Object[] res = odoo.readFromModel("purchase.order", Collections.singletonMap("fields", Arrays.asList("name")), 10);

        assertArrayEquals(expected, res);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

/**
     * Verifica la propagazione delle eccezioni durante la lettura.
     */
    @Test(expected = XmlRpcException.class)
    public void readFromModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.readFromModel("purchase.order", null, 1, 2, 3);
    }

/**
     * Verifica che l'aggiornamento di un record {@code updateOnModel} restituisca {@code true}
     * quando l'operazione ha successo su Odoo.
     */
    @Test
    public void updateOnModel_returnsBooleanFromModelsExecute() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(Boolean.TRUE);

        boolean ok = odoo.updateOnModel("purchase.order", Collections.singletonMap("x_studio_oaf","SHIPPED"), 55);

        assertTrue(ok);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

/**
     * Verifica la propagazione delle eccezioni durante l'aggiornamento.
     */
    @Test(expected = XmlRpcException.class)
    public void updateOnModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.updateOnModel("purchase.order", new HashMap<>(), 77);
    }

/**
     * Verifica che l'inserimento di un nuovo record {@code insertOnModel} restituisca l'ID (intero)
     * del record appena creato.
     */
    @Test
    public void insertOnModel_returnsIntFromModelsExecute() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList())).thenReturn(987);

        int id = odoo.insertOnModel("mail.message", Collections.singletonMap("body","msg"));

        assertEquals(987, id);
        verify(models, times(1)).execute(eq(OdooApiConfig.EXECUTE_KW), anyList());
    }

/**
     * Verifica la propagazione delle eccezioni durante l'inserimento.
     */
    @Test(expected = XmlRpcException.class)
    public void insertOnModel_propagatesXmlRpcException() throws Exception {
        when(models.execute(eq(OdooApiConfig.EXECUTE_KW), anyList()))
                .thenThrow(new XmlRpcException("boom"));

        odoo.insertOnModel("mail.message", new HashMap<>());
    }
    
}