package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Prezzi fissi per il prodotto (tasse e prezzo base)
 */
@JacksonXmlRootElement(localName="PRODUCT_PRICE_FIX")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlProductPriceFix {
	
	/**
	 * Prezzo netto più supplementi e sconti per unità di misura di base per pezzo o metro

	 */
	@JacksonXmlProperty(localName="bmecat:PRICE_AMOUNT")
	private float priceAmount;
	
	/**
	 * Quantità di riferimento del prezzo

	 */
	@JacksonXmlProperty(localName="bmecat:PRICE_QUANTITY")
	private int priceQuantity;
	
	/**
	 * dettagli tasse
	 */
	@JacksonXmlProperty(localName="TAX_DETAILS_FIX")
	private XmlTaxDetailsFix taxDetailsFix;
	
	/**
	 * dettagli prezzo base
	 */
	@JacksonXmlProperty(localName="PRICE_BASE_FIX")
	private XmlPriceBaseFix priceBaseFix;
	
	/**
	 * 
	 * @return float
	 */
	public float getPriceAmount() {
		return priceAmount;
	}

	/**
	 * 
	 * @param priceAmount - float
	 */
	public void setPriceAmount(final float priceAmount) {
		this.priceAmount = priceAmount;
	}

	/**
	 * 
	 * @return int
	 */
	public int getPriceQuantity() {
		return priceQuantity;
	}

	/**
	 * 
	 * @param priceQuantity int
	 */
	public void setPriceQuantity(final int priceQuantity) {
		this.priceQuantity = priceQuantity;
	}

	/**
	 * 
	 * @return XmlTaxDetailsFix
	 */
	public XmlTaxDetailsFix getTaxDetailsFix() {
		return taxDetailsFix;
	}

	/**
	 * 
	 * @param taxDetailsFix - XmlTaxDetailsFix
	 */
	public void setTaxDetailsFix(final XmlTaxDetailsFix taxDetailsFix) {
		this.taxDetailsFix = taxDetailsFix;
	}

	/**
	 * 
	 * @return XmlPriceBaseFix
	 */
	public XmlPriceBaseFix getPriceBaseFix() {
		return priceBaseFix;
	}

	/**
	 * 
	 * @param priceBaseFix - XmlPriceBaseFix
	 */
	public void setPriceBaseFix(final XmlPriceBaseFix priceBaseFix) {
		this.priceBaseFix = priceBaseFix;
	}

	
}
