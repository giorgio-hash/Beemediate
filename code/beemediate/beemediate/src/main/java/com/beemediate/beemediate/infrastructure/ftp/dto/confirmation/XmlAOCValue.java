package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;

/**
 * Importo supplemento/sconto
 */
public class XmlAOCValue{
	
	/**
	 * Importo supplemento/sconto

	 */
	@JacksonXmlProperty(localName="AOC_MONETARY_AMOUNT")
	private float amount;

	/**
	 * 
	 * @return float
	 */
	public float getAmount() {
		return amount;
	}

	/**
	 * 
	 * @param amount - float
	 */
	public void setAmount(float amount) {
		this.amount = amount;
	}
}
