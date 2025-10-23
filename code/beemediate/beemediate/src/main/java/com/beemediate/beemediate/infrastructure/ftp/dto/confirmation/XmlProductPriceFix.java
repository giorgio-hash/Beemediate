package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName="PRODUCT_PRICE_FIX")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlProductPriceFix {
	
	
	@JacksonXmlProperty(localName="bmecat:PRICE_AMOUNT")
	private float priceAmount;
	
	@JacksonXmlProperty(localName="bmecat:PRICE_QUANTITY")
	private int priceQuantity;
	
	@JacksonXmlProperty(localName="TAX_DETAILS_FIX")
	private XmlTaxDetailsFix taxDetailsFix;
	
	@JacksonXmlProperty(localName="PRICE_BASE_FIX")
	private XmlPriceBaseFix priceBaseFix;
	

	public float getPriceAmount() {
		return priceAmount;
	}

	public void setPriceAmount(float priceAmount) {
		this.priceAmount = priceAmount;
	}

	public int getPriceQuantity() {
		return priceQuantity;
	}

	public void setPriceQuantity(int priceQuantity) {
		this.priceQuantity = priceQuantity;
	}

	public XmlTaxDetailsFix getTaxDetailsFix() {
		return taxDetailsFix;
	}

	public void setTaxDetailsFix(XmlTaxDetailsFix taxDetailsFix) {
		this.taxDetailsFix = taxDetailsFix;
	}

	public XmlPriceBaseFix getPriceBaseFix() {
		return priceBaseFix;
	}

	public void setPriceBaseFix(XmlPriceBaseFix priceBaseFix) {
		this.priceBaseFix = priceBaseFix;
	}

	

}
