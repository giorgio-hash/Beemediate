package com.beemediate.beemediate.controller.http;


import static com.github.tomakehurst.wiremock.client.WireMock.aResponse;
import static com.github.tomakehurst.wiremock.client.WireMock.get;
import static com.github.tomakehurst.wiremock.client.WireMock.stubFor;
import static com.github.tomakehurst.wiremock.client.WireMock.urlEqualTo;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.time.Duration;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.chrome.ChromeDriver;
import org.openqa.selenium.chrome.ChromeOptions;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.boot.test.web.server.LocalServerPort;

import com.github.tomakehurst.wiremock.WireMockServer;
import com.github.tomakehurst.wiremock.client.WireMock;

/**
 * Test di integrazione per l'interfaccia utente di Beemediate.
 * 
 * Questa classe testa il comportamento del frontend in relazione allo stato del backend,
 * utilizzando WireMock per simulare i servizi remoti e Selenium WebDriver per l'automazione del browser.
 * 
 * <p><b>Setup:</b>
 * <ul>
 *   <li>WireMock è configurato su porta 8888 per intercettare e mockare le chiamate HTTP</li>
 *   <li>ChromeDriver in modalità headless per eseguire i test in ambiente CI/CD</li>
 *   <li>Spring Boot avvia l'applicazione su una porta casuale (iniettata via @LocalServerPort)</li>
 * </ul>
 * 
 * <p><b>Ciclo di vita:</b>
 * <ul>
 *   <li>{@code @BeforeAll}: Inizializza l'istanza statica di WireMockServer</li>
 *   <li>{@code @BeforeEach}: Riavvia WireMock se necessario, resetta gli stub, e inizializza il driver</li>
 *   <li>{@code @AfterEach}: Chiude il browser (WireMock rimane attivo per il prossimo test)</li>
 *   <li>{@code @AfterAll}: Arresta completamente il server WireMock</li>
 * </ul>
 * 
 * <p><b>Scenari testati:</b>
 * <ul>
 *   <li>Backend online con caricamento ordini</li>
 *   <li>Backend online con verifica conferme</li>
 *   <li>Gestione errori HTTP 500</li>
 *   <li>Rilevamento offline del backend e aggiornamento stato UI</li>
 *   <li>Blocco preventivo delle azioni quando backend è offline</li>
 * </ul>
 * 
 * @author Beemediate Team
 * @version 1.0
 */
@SpringBootTest(webEnvironment = SpringBootTest.WebEnvironment.RANDOM_PORT)
class BeemediateUITest {

    /**
     * Porta del server Spring Boot, iniettata automaticamente.
     */
    @LocalServerPort
    private int port;

    /**
     * WebDriver Selenium per l'automazione del browser.
     */
    private WebDriver driver;

    /**
     * Page Object per l'interazione con la UI di Beemediate.
     */
    private BeemediatePage page;
    
    /**
     * Istanza statica di WireMockServer per mockare i servizi remoti.
     * Lo stato viene gestito nei metodi @BeforeEach e nei test stessi.
     */
    private static WireMockServer wireMockServer;

    /**
     * Inizializza il server WireMock sulla porta 8888.
     * Eseguito una sola volta prima di tutti i test.
     */
    @BeforeAll
    static void initServerObject() {
        wireMockServer = new WireMockServer(8888);
    }

    /**
     * Arresta il server WireMock se è in esecuzione.
     * Eseguito una sola volta dopo tutti i test.
     */
    @AfterAll
    static void shutdownServer() {
        if (wireMockServer != null && wireMockServer.isRunning()) {
            wireMockServer.stop();
        }
    }

    /**
     * Setup eseguito prima di ogni test.
     * 
     * <p>Operazioni:
     * <ul>
     *   <li>Riavvio di WireMock se un test precedente lo ha spento</li>
     *   <li>Reset degli stub per evitare interferenze tra test</li>
     *   <li>Configurazione e avvio del browser Chrome</li>
     *   <li>Istanziazione del Page Object</li>
     * </ul>
     */
    @BeforeEach
    void setup() {
        // 1. GARANZIA DI AVVIO: Se un test precedente ha spento il server, lo riaccendiamo ora.
        if (!wireMockServer.isRunning()) {
            wireMockServer.start();
        }
        
        // 2. Reset configurazione: Pulisce gli stub vecchi per non avere interferenze
        WireMock.configureFor("localhost", 8888);
        wireMockServer.resetAll();

        // 3. Setup Browser
        ChromeOptions options = new ChromeOptions();
        options.addArguments("--headless=new");
        options.addArguments("--no-sandbox");
        options.addArguments("--disable-dev-shm-usage");
        options.addArguments("--remote-allow-origins=*");

        driver = new ChromeDriver(options);
        page = new BeemediatePage(driver);
    }

    /**
     * Cleanup eseguito dopo ogni test.
     * Chiude il browser ma mantiene WireMock attivo per i test successivi.
     */
    @AfterEach
    void tearDown() {
        if (driver != null) {
            driver.quit();
        }
        // Non fermare WireMock qui, altrimenti rallenti i test che lo vogliono acceso.
    }

    /**
     * Test del flusso con backend online e caricamento ordini.
     * 
     * <p>Verifica che:
     * <ul>
     *   <li>Lo stato del backend sia visualizzato correttamente come online</li>
     *   <li>Il caricamento degli ordini funzioni e ritorni il testo previsto</li>
     * </ul>
     */
    @Test
    @DisplayName("Test flusso: Backend Online e Caricamento Ordini")
    void testBackendOnlineAndOrders() {
        stubFor(get(urlEqualTo("/manage/orders"))
                .willReturn(aResponse()
                        .withStatus(200)
                        .withHeader("Access-Control-Allow-Origin", "*")
                        .withBody("Ordini caricati: 150")));
        stubFor(get(urlEqualTo("/manage/healthcheck"))
                .willReturn(aResponse()
                        .withStatus(200)
                        .withHeader("Access-Control-Allow-Origin", "*")));

        page.open("http://localhost:" + port);

        page.waitForBackendOnline();
        assertEquals("Backend attiva", page.getStatusText());
        assertEquals("status-dot status-online", page.getStatusDotClass());

        page.clickLoadOrders();

        String response = page.getResponseText();
        assertTrue(response.contains("Ordini caricati: 150"), "Il testo della risposta non corrisponde");
    }
    
    /**
     * Test del flusso con backend online e verifica conferme.
     * 
     * <p>Verifica che:
     * <ul>
     *   <li>Lo stato del backend sia online</li>
     *   <li>La verifica delle conferme ritorni il testo atteso con il prefisso dell'endpoint</li>
     * </ul>
     */
    @Test
    @DisplayName("Test flusso: Backend Online e Verifica Conferme")
    void testBackendOnlineAndConfirmations() {

        stubFor(get(urlEqualTo("/manage/healthcheck"))
                .willReturn(aResponse()
                        .withStatus(200)
                        .withHeader("Access-Control-Allow-Origin", "*")));

        stubFor(get(urlEqualTo("/manage/confirmations"))
                .willReturn(aResponse()
                        .withStatus(200)
                        .withHeader("Access-Control-Allow-Origin", "*")
                        .withBody("Check conferme completato: 42 conferme elaborate.")));

        page.open("http://localhost:" + port);

        page.waitForBackendOnline();
        assertEquals("status-dot status-online", page.getStatusDotClass());

        page.clickCheckConfirmations();

        String response = page.getResponseText();
        
        assertTrue(response.contains("Check conferme completato: 42"), 
            "Il box risposta dovrebbe contenere il messaggio restituito dal mock");
            
        assertTrue(response.contains("Risposta da /manage/confirmations:"),
            "Il frontend dovrebbe aggiungere il prefisso indicante l'endpoint chiamato");
    }

    /**
     * Test della gestione di un errore HTTP 500 specifico.
     * 
     * <p>Verifica che:
     * <ul>
     *   <li>Un errore 500 sia gestito elegantemente dal frontend</li>
     *   <li>All'utente venga mostrato un messaggio di errore comprensibile</li>
     * </ul>
     */
    @Test
    @DisplayName("Test flusso: Gestione Errore 500 specifico")
    void testSpecificErrorHandling() {
        stubFor(get(urlEqualTo("/manage/orders"))
                .willReturn(aResponse()
                        .withStatus(500)
                        .withHeader("Access-Control-Allow-Origin", "*")));
        
        stubFor(get(urlEqualTo("/manage/healthcheck"))
                .willReturn(aResponse()
                        .withStatus(200)
                        .withHeader("Access-Control-Allow-Origin", "*")));

        page.open("http://localhost:" + port);
        page.waitForBackendOnline();

        page.clickLoadOrders();

        String response = page.getResponseText();


        assertEquals("C'è stato un problema durante la procedura. Controlla la connessione ai servizi remoti e riprova.", 
                response, 
                "Dovrebbe mostrare il messaggio utente amichevole");
    }

    /**
     * Test del rilevamento e visualizzazione dello stato offline del backend.
     * 
     * <p>Simula uno scenario in cui il backend è inizialmente online ma poi diventa offline.
     * Verifica che l'UI si aggiorni correttamente con lo stato offline.
     */
    @Test
    @DisplayName("Test flusso: Backend Offline")
    void testBackendOffline() {
        // Setup iniziale: tutto OK
        stubFor(get(urlEqualTo("/manage/healthcheck"))
                .willReturn(aResponse().withStatus(200).withHeader("Access-Control-Allow-Origin", "*")));

        page.open("http://localhost:" + port);
        page.waitForBackendOnline();

        // AZIONE: Simulazione crash
        System.out.println("Simulazione crash backend...");
        wireMockServer.stop(); 


        WebDriverWait longWait = new WebDriverWait(driver, Duration.ofSeconds(8));
        longWait.until(d -> page.getStatusDotClass().contains("status-offline"));
        
        assertEquals("Backend non raggiungibile", page.getStatusText());
        assertEquals("status-dot status-offline", page.getStatusDotClass());
    }
    
    /**
     * Test del blocco preventivo dei pulsanti operativi quando il backend è offline.
     * 
     * <p>Verifica che:
     * <ul>
     *   <li>I pulsanti non inviino richieste quando il backend è offline</li>
     *   <li>Un messaggio di errore appropriato sia visualizzato all'utente</li>
     * </ul>
     */
    @Test
    @DisplayName("Bottoni Operativi: Blocco preventivo quando Backend è Offline")
    void testButtonsActionWhenOffline() {
        // AZIONE: Assicuro che sia spento fin da subito
        if (wireMockServer.isRunning()) {
            wireMockServer.stop();
        }

        page.open("http://localhost:" + port);

        WebDriverWait wait = new WebDriverWait(driver, Duration.ofSeconds(5));
        wait.until(d -> page.getStatusDotClass().contains("status-offline"));

        String expectedErrorMsg = "Impossibile contattare Beemediate. La richiesta non è stata inviata.";

        page.clickLoadOrders();
        
        wait.until(ExpectedConditions.textToBePresentInElementLocated(page.getresponseBox(), expectedErrorMsg));
        assertEquals(expectedErrorMsg, page.getResponseText());

        page.clickCheckConfirmations();

        wait.until(ExpectedConditions.textToBePresentInElementLocated(page.getresponseBox(), expectedErrorMsg));
        assertEquals(expectedErrorMsg, page.getResponseText());
    }
}