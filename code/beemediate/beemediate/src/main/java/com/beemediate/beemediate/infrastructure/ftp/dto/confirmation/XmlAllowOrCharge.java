package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName="ALLOW_OR_CHARGE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlAllowOrCharge {
	
	@JacksonXmlProperty(isAttribute=true)
	private String type;
	
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_NAME")
	private String name;
	
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_DESCR")
	private String descr;
	
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_VALUE")
	private XmlAOCValue value;
	
	public class XmlAOCValue{
		
		@JacksonXmlProperty(localName="AOC_MONETARY_AMOUNT")
		private float amount;

		public float getAmount() {
			return amount;
		}

		public void setAmount(float amount) {
			this.amount = amount;
		}
	}

	public XmlAOCValue getValue() {
		return value;
	}

	public void setValue(XmlAOCValue value) {
		this.value = value;
	}

	public String getName() {
		return name;
	}

	public String getDescr() {
		return descr;
	}
	
	public String gettype() {
		return type;
	}
	
	public void setType(String type) {
		this.type = type;
	}
}
