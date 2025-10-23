package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName="ORDERRESPONSE_SUMMARY")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseSummary {
	
	@JacksonXmlProperty(localName="TOTAL_ITEM_NUM")
	private int totalItemNum;
	
	@JacksonXmlProperty(localName="TOTAL_AMOUNT")
	private float totalAmount;
	
	@JacksonXmlElementWrapper(localName = "ALLOW_OR_CHARGES_FIX", useWrapping = true)
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE")
	private List<XmlAllowOrCharge> allowOrChargesFix;

	
	public int getTotalItemNum() {
		return totalItemNum;
	}

	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	public float getTotalAmount() {
		return totalAmount;
	}

	public void setTotalAmount(float totalAmount) {
		this.totalAmount = totalAmount;
	}

	public List<XmlAllowOrCharge> getAllowOrChargesFix() {
		return allowOrChargesFix;
	}

	public void setAllowOrChargesFix(List<XmlAllowOrCharge> allowOrChargesFix) {
		this.allowOrChargesFix = allowOrChargesFix;
	}
	
	
}
