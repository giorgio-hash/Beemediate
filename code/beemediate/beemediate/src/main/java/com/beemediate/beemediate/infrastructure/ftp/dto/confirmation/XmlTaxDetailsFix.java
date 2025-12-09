package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;

/**
 * Componente della struttura XML ORDERRESPONSE. Specifica i dettagli relativi a tasse ed imposte aggiuntive al prezzo base dell'ordine.
 */
public class XmlTaxDetailsFix{
	
	/**
	 * Aliquota IVA (%)
	 */
	@JacksonXmlProperty(localName="bmecat:TAX")
	private float tax;
	
	/**
	 * Importo dell'imposta a valle

	 */
	@JacksonXmlProperty(localName="TAX_AMOUNT")
	private float taxAmount;

	/**
	 * 
	 * @return float
	 */
	public float getTax() {
		return tax;
	}

	/**
	 * 
	 * @param tax - float
	 */
	public void setTax(final float tax) {
		this.tax = tax;
	}

	/**
	 * 
	 * @return float
	 */
	public float getTaxAmount() {
		return taxAmount;
	}

	/**
	 * 
	 * @param taxAmount - float
	 */
	public void setTaxAmount(final float taxAmount) {
		this.taxAmount = taxAmount;
	}
	
	
	
}