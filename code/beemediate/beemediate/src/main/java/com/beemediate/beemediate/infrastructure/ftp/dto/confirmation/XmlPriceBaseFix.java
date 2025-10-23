package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName="PRICE_BASE_FIX")
public class XmlPriceBaseFix{
	
	@JacksonXmlProperty(localName="PRICE_UNIT_VALUE")
	private float price;
	
	@JacksonXmlProperty(localName="bmecat:PRICE_UNIT")
	private String priceUnit;

	public float getPrice() {
		return price;
	}

	public void setPrice(float price) {
		this.price = price;
	}

	public String getPriceUnit() {
		return priceUnit;
	}

	public void setPriceUnit(String priceUnit) {
		this.priceUnit = priceUnit;
	}
	
	
}