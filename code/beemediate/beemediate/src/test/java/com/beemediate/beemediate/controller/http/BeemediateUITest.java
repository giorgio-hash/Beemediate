package com.beemediate.beemediate.controller.http;


import com.github.tomakehurst.wiremock.WireMockServer;
import com.github.tomakehurst.wiremock.client.WireMock;
import org.junit.jupiter.api.*;
import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.chrome.ChromeDriver;
import org.openqa.selenium.chrome.ChromeOptions;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.boot.test.web.server.LocalServerPort;

import java.time.Duration;

import static com.github.tomakehurst.wiremock.client.WireMock.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@SpringBootTest(webEnvironment = SpringBootTest.WebEnvironment.RANDOM_PORT)
class BeemediateUITest {

    @LocalServerPort
    private int port;

    private WebDriver driver;
    private BeemediatePage page;
    
    // Istanza statica, ma la gestione dello stato avviene nei metodi Each
    private static WireMockServer wireMockServer;

    @BeforeAll
    static void initServerObject() {
        wireMockServer = new WireMockServer(8888);
    }

    @AfterAll
    static void shutdownServer() {
        if (wireMockServer != null && wireMockServer.isRunning()) {
            wireMockServer.stop();
        }
    }

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

    @AfterEach
    void tearDown() {
        if (driver != null) {
            driver.quit();
        }
        // Non fermare WireMock qui, altrimenti rallenti i test che lo vogliono acceso.
    }

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