package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;

public class XmlTaxDetailsFix{
	
	@JacksonXmlProperty(localName="bmecat:TAX")
	private float tax;
	
	@JacksonXmlProperty(localName="TAX_AMOUNT")
	private float taxAmount;

	public float getTax() {
		return tax;
	}

	public void setTax(float tax) {
		this.tax = tax;
	}

	public float getTaxAmount() {
		return taxAmount;
	}

	public void setTaxAmount(float taxAmount) {
		this.taxAmount = taxAmount;
	}
	
	
	
}