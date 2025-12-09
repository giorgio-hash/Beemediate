package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * dettagli prezzo base
 */
@JacksonXmlRootElement(localName="PRICE_BASE_FIX")
public class XmlPriceBaseFix{
	
	/**
	 * Unità di prezzo consegnata

	 */
	@JacksonXmlProperty(localName="PRICE_UNIT_VALUE")
	private float price;

	/**
	 * Unità di misura a cui si riferisce il prezzo

	 */
	@JacksonXmlProperty(localName="bmecat:PRICE_UNIT")
	private String priceUnit;

	
	/**
	 * 
	 * @return float
	 */
	public float getPrice() {
		return price;
	}

	/**
	 * 
	 * @param price - float
	 */
	public void setPrice(final float price) {
		this.price = price;
	}

	/**
	 * 
	 * @return String
	 */
	public String getPriceUnit() {
		return priceUnit;
	}

	/**
	 * 
	 * @param priceUnit - String
	 */
	public void setPriceUnit(final String priceUnit) {
		this.priceUnit = priceUnit;
	}
	
	
}