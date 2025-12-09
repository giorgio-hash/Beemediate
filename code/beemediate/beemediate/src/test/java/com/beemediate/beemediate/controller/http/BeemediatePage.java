package com.beemediate.beemediate.controller.http;

import java.time.Duration;

import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;

/**
 * Page Object Model class for the Beemediate UI page.
 * Provides methods to interact with and verify the state of the Beemediate web interface.
 * 
 * This class encapsulates locators and interaction methods for the Beemediate UI,
 * including status monitoring, order management, and confirmation checking.
 */
public class BeemediatePage {
    
    /**
     * WebDriver instance used to control the browser.
     */
    private final WebDriver driver;
    
    /**
     * WebDriverWait instance configured with a 10-second timeout.
     * Used for explicit waits on UI elements.
     */
    private final WebDriverWait wait;

    /**
     * Locator for the status text element (id: "status-text").
     */
    private final By statusText = By.id("status-text");
    
    /**
     * Locator for the status dot element (CSS selector: ".status-dot").
     */
    private final By statusDot = By.cssSelector(".status-dot");
    
    /**
     * Locator for the orders button element (id: "ordersBtn").
     */
    private final By ordersBtn = By.id("ordersBtn");
    
    /**
     * Locator for the confirmations button element (id: "confBtn").
     */
    private final By confBtn = By.id("confBtn");
    
    /**
     * Locator for the response box element (id: "response").
     */
    private final By responseBox = By.id("response");

    /**
     * Constructs a BeemediatePage instance.
     * Initializes the WebDriver and WebDriverWait with a 10-second timeout.
     * 
     * @param driver the WebDriver instance to control the browser
     */
    public BeemediatePage(WebDriver driver) {
        this.driver = driver;
        this.wait = new WebDriverWait(driver, Duration.ofSeconds(10));
    }

    /**
     * Navigates to the Beemediate UI page.
     * 
     * @param baseUrl the base URL of the application
     */
    public void open(String baseUrl) {
        driver.get(baseUrl + "/beemediate-ui.html");
    }

    /**
     * Waits for the backend status to become "Backend attiva".
     * Uses polling to check the UI status text element.
     */
    public void waitForBackendOnline() {
        wait.until(ExpectedConditions.textToBePresentInElementLocated(statusText, "Backend attiva"));
    }

    /**
     * Clicks the "Load Orders" button.
     * Waits until the button is clickable before performing the action.
     */
    public void clickLoadOrders() {
        wait.until(ExpectedConditions.elementToBeClickable(ordersBtn)).click();
    }

    /**
     * Clicks the "Check Confirmations" button.
     * Waits until the button is clickable before performing the action.
     */
    public void clickCheckConfirmations() {
        wait.until(ExpectedConditions.elementToBeClickable(confBtn)).click();
    }

    /**
     * Returns the locator for the response box element.
     * 
     * @return the By locator for the response box
     */
    public By getresponseBox() {
        return responseBox;
    }
    
    /**
     * Retrieves the response text from the response box.
     * Waits until the text is no longer the default message "Risposta dal server...".
     * 
     * @return the text content of the response box
     */
    public String getResponseText() {
        // Attende che il testo non sia quello di default ("Risposta dal server...")
        wait.until(ExpectedConditions.not(
            ExpectedConditions.textToBe(responseBox, "Risposta dal server...")
        ));
        return driver.findElement(responseBox).getText();
    }
    
    /**
     * Retrieves the CSS class attribute of the status dot element.
     * 
     * @return the class attribute value of the status dot
     */
    public String getStatusDotClass() {
        return driver.findElement(statusDot).getAttribute("class");
    }
    
    /**
     * Retrieves the status text from the status text element.
     * 
     * @return the text content of the status text element
     */
    public String getStatusText() {
        return driver.findElement(statusText).getText();
    }
}