package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Supplemento o sconto
 */
@JacksonXmlRootElement(localName="ALLOW_OR_CHARGE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlAllowOrCharge {
	
	/**
	 * tipo di supplemento (ad es."surcharge")
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String type;
	
	/**
	 * Indicatore supplemento inflazione

	 */
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_NAME")
	private String name;

	/**
	 * Descrizione del testo

	 */
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_DESCR")
	private String descr;

	/**
	 * Importo supplemento/sconto

	 */
	@JacksonXmlProperty(localName="ALLOW_OR_CHARGE_VALUE")
	private XmlAOCValue value;
	
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

	/**
	 * 
	 * @return XmlAOCValue
	 */
	public XmlAOCValue getValue() {
		return value;
	}

	/**
	 * 
	 * @param value - XmlAOCValue
	 */
	public void setValue(XmlAOCValue value) {
		this.value = value;
	}

	/**
	 * 
	 * @return String
	 */
	public String getName() {
		return name;
	}

	/**
	 * 
	 * @return String
	 */
	public String getDescr() {
		return descr;
	}
	
	/**
	 * 
	 * @return String
	 */
	public String gettype() {
		return type;
	}
	
	/**
	 * 
	 * @param type - String
	 */
	public void setType(String type) {
		this.type = type;
	}
}
