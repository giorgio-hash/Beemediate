package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Mappatura XML-OpenTrans con identificativi del prodotto per ogni partner commerciale coinvolto nella transazione
 */
@JacksonXmlRootElement(localName = "PRODUCT_ID")
public class XmlProductID{	
	
	/**
	 * tag per Numero di articolo del fornitore
	 */
	@JacksonXmlProperty(localName="bmecat:SUPPLIER_PID")
	private XmlPartyID supplierId;
	
	/**
	 * Riferimento a BuyerID per tag numero di articolo del cliente (opzionale)
	 */
	@JacksonXmlProperty(localName="bmecat:BUYER_PID")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlPartyID buyerId;
	
	/**
	 * Tag contenente descrizione prodotto 
	 */
	@JacksonXmlProperty(localName="bmecat:DESCRIPTION_SHORT")
	@JsonInclude(JsonInclude.Include.NON_EMPTY)
	private String descriptionShort;

	/**
	 * empty costructor for Jackson deserializer
	 */
	public XmlProductID() {/*empty costructor for Jackson deserializer*/}
	
	
	/**
	 * Costruttore
	 * @param supplierId - identificativo dell'articolo sul sistema fornitore
	 * @param buyerId - identificativo dell'articolo sul sistema cliente
	 * @param descriptionShort - descrizione dell'articolo
	 */
	public XmlProductID(String supplierId, String buyerId, String descriptionShort) {
		super();
		if(supplierId==null || supplierId.isEmpty() || supplierId.isBlank())
			this.supplierId = null;
		else
			this.supplierId = new XmlPartyID(supplierId);
			
		if(buyerId==null || buyerId.isEmpty() || buyerId.isBlank())
			this.buyerId = null;
		else {
			this.buyerId = new XmlPartyID(buyerId);
			this.buyerId.setType("CODE");
		}
		
		this.descriptionShort = descriptionShort;
	}

	/**
	 * 
	 * @return String
	 */
	public XmlPartyID getSupplierId() {
		return supplierId;
	}

	/**
	 * 
	 * @return BuyerID con identificativo ordine
	 */
	public void setSupplierId(XmlPartyID supplierId) {
		this.supplierId = supplierId;
	}

	/**
	 * 
	 * @return String
	 */
	public XmlPartyID getBuyerId() {
		return buyerId;
	}

	public void setBuyerId(XmlPartyID buyerId) {
		this.buyerId = buyerId;
	}

	public String getDescriptionShort() {
		return descriptionShort;
	}

	public void setDescriptionShort(String descriptionShort) {
		this.descriptionShort = descriptionShort;
	}

}