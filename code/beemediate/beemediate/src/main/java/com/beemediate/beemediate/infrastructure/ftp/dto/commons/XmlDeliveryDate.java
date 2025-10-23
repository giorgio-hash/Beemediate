package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per struttura informazioni relative alle date per la consegna desiderati dal cliente.
 */
@JacksonXmlRootElement(localName = "DELIVERY_DATE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlDeliveryDate{
	
	/**
	 * Attributo obbligatorio per conformità col formato XML-OpenTrans del fornitore
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String type;
	
	/*
	 * Data inizio periodo di consegna desiderata dal cliente (N.B. è richiesto sia uguale a DELIVERY_END_DATE)
	 */
	@JacksonXmlProperty(localName="DELIVERY_START_DATE")
	private String deliveryStartDate;
	
	/*
	 * Data fine periodo di consegna desiderata dal cliente (N.B. è richiesto sia uguale a DELIVERY_START_DATE)
	 */
	@JacksonXmlProperty(localName="DELIVERY_END_DATE")
	private String deliveryEndDate;
	
	/**
	 * Specifica il tipo di DeliveryDate
	 */
	public enum DeliveryDateType{
		OPTIONAL("optional"),FIXED("fixed");
		
		/**
		 * valore String
		 */
		private final String type;
		
		/**
		 * Costruttore private
		 * @param type - valore String corrispondente
		 */
		DeliveryDateType(String type){
			this.type=type;
		}
		
		@Override
		public String toString() {
			return type;
		}
	}
	
	/**
	 * Empty Constructor for Jackson deserializer 
	 */
	public XmlDeliveryDate() {/**Empty Constructor for Jackson deserializer*/}
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans data di consegna
	 * @param deliveryStartDate - String con data in formato opportuno
	 * @param deliveryEndDate - String con data in formato opportuno
	 * @param type - DeliveryDateType
	 */
	public XmlDeliveryDate(String deliveryStartDate, String deliveryEndDate, DeliveryDateType type) {
		super();
		this.deliveryStartDate = deliveryStartDate;
		this.deliveryEndDate = deliveryEndDate;
		this.type = type.toString();
	}

	/**
	 * 
	 * @return String specificante data
	 */
	public String getDeliveryStartDate() {
		return deliveryStartDate;
	}

	/**
	 * 
	 * @return String specificante data
	 */
	public String getDeliveryEndDate() {
		return deliveryEndDate;
	}
	
	/**
	 * 
	 * @return formato String del valore specificato in DeliveryDateType
	 */
	public String getType() {
		return type;
	}

	/**
	 * 
	 * @param deliveryStartDate - data di consegna (uguale a deliveryEndDate)
	 */
	public void setDeliveryStartDate(String deliveryStartDate) {
		this.deliveryStartDate = deliveryStartDate;
	}

	/**
	 * 
	 * @param deliveryStartDate - data di consegna (uguale a deliveryStartDate)
	 */
	public void setDeliveryEndDate(String deliveryEndDate) {
		this.deliveryEndDate = deliveryEndDate;
	}
	
	/**
	 * 
	 * @param type - valore String di DeliveryDateType
	 */
	public void setType(String type) {
		this.type = type;
	}
	
}

