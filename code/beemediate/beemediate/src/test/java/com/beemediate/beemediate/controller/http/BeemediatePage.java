package com.beemediate.beemediate.controller.http;

import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.WebElement;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;

import java.time.Duration;

public class BeemediatePage {
    private final WebDriver driver;
    private final WebDriverWait wait;

    // Locators
    private final By statusText = By.id("status-text");
    private final By statusDot = By.cssSelector(".status-dot");
    private final By ordersBtn = By.id("ordersBtn");
    private final By confBtn = By.id("confBtn");
    private final By responseBox = By.id("response");

    public BeemediatePage(WebDriver driver) {
        this.driver = driver;
        this.wait = new WebDriverWait(driver, Duration.ofSeconds(10));
    }

    public void open(String baseUrl) {
        driver.get(baseUrl + "/beemediate-ui.html");
    }

    // Attende che lo stato diventi "Backend attiva" (polling UI)
    public void waitForBackendOnline() {
        wait.until(ExpectedConditions.textToBePresentInElementLocated(statusText, "Backend attiva"));
    }

    public void clickLoadOrders() {
        wait.until(ExpectedConditions.elementToBeClickable(ordersBtn)).click();
    }

    public void clickCheckConfirmations() {
        wait.until(ExpectedConditions.elementToBeClickable(confBtn)).click();
    }

    public By getresponseBox() {
    	return responseBox;
    }
    
    public String getResponseText() {
        // Attende che il testo non sia quello di default ("Risposta dal server...")
        wait.until(ExpectedConditions.not(
            ExpectedConditions.textToBe(responseBox, "Risposta dal server...")
        ));
        return driver.findElement(responseBox).getText();
    }
    
    public String getStatusDotClass() {
        return driver.findElement(statusDot).getAttribute("class");
    }
    
    public String getStatusText() {
        return driver.findElement(statusText).getText();
    }
}