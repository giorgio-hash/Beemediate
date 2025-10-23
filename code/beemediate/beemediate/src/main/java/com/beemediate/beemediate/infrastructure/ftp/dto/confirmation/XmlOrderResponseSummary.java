package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Riepilogo dell'ordine

 */
@JacksonXmlRootElement(localName="ORDERRESPONSE_SUMMARY")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseSummary {

	/**
	 * Numero di articoli dell'ordine

	 */
	@JacksonXmlProperty(localName="TOTAL_ITEM_NUM")
	private int totalItemNum;

	/**
	 * Importo totale lordo finale

	 */
	@JacksonXmlProperty(localName="TOTAL_AMOUNT")
	private float totalAmount;
	
	/**
	 * 	lista di supplementi/sconti
	 */
	@JacksonXmlElementWrapper(localName = "ALLOW_OR_CHARGES_FIX", useWrapping = true)
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE")
	private List<XmlAllowOrCharge> allowOrChargesFix;

	
	/**
	 * 
	 * @return int
	 */
	public int getTotalItemNum() {
		return totalItemNum;
	}

	/**
	 * 
	 * @param totalItemNum - int
	 */
	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	/**
	 * 
	 * @return float
	 */
	public float getTotalAmount() {
		return totalAmount;
	}

	/**
	 * 
	 * @param totalAmount - float
	 */
	public void setTotalAmount(float totalAmount) {
		this.totalAmount = totalAmount;
	}

	/**
	 * 
	 * @return XmlAllowOrCharge
	 */
	public List<XmlAllowOrCharge> getAllowOrChargesFix() {
		return allowOrChargesFix;
	}

	/**
	 * 
	 * @param allowOrChargesFix - {@code List} di {@code XmlAllowOrCharge}
	 */
	public void setAllowOrChargesFix(List<XmlAllowOrCharge> allowOrChargesFix) {
		this.allowOrChargesFix = allowOrChargesFix;
	}
	
	
}
