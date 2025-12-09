package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlOrderPartiesReference;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
/**
 * Informazioni della transazione
 */
@JacksonXmlRootElement(localName = "ORDERRESPONSE_INFO")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseInfo {
	
	/**
	 * Numero d'ordine del fornitore
	 */
	@JacksonXmlProperty(localName="SUPPLIER_ORDER_ID")
	private String supplierOrderId;
	
	/**
	 * Data di conferma dell'ordine
	 */
	@JacksonXmlProperty(localName="ORDERRESPONSE_DATE")
	private String orderResponseDate;
	
	/**
	 * Numero d'ordine del cliente
	 */
	@JacksonXmlProperty(localName="ORDER_ID")
	private String orderId;
	
	/**
	 * Data dell'ordine del cliente
	 */
	@JacksonXmlProperty(localName="ORDER_DATE")
	private String orderDate;
	
	/**
	 * Riferimento alla ricevuta d'ordine elettronica
	 */
	@JacksonXmlProperty(localName="ALT_CUSTOMER_ORDER_ID")
	private String altCustomerOrderId;
	
	/**
	 * Dati di rifeimento sintetici delle parti
	 */
	@JacksonXmlProperty(localName="ORDER_PARTIES_REFERENCE")
	private XmlOrderPartiesReference orderPartiesReference;
	
	/**
	 * Valuta
	 */
	@JacksonXmlProperty(localName="bmecat:CURRENCY")
	private String currency;
	
	/**
	 * Data di consegna
	 */
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private XmlDeliveryDate deliveryDate;
	
	/**
	 * Partner commerciale
	 */
    @JacksonXmlElementWrapper(localName = "PARTIES", useWrapping = true) 
    @JacksonXmlProperty(localName = "PARTY")
	private List<XmlParty> parties;
	
    /**
     * Numero di commissione del cliente
     */
	@JacksonXmlProperty(localName="REMARKS")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlRemarks remarks;

	/**
	 * 
	 * @return String
	 */
	public String getSupplierOrderId() {
		return supplierOrderId;
	}

	/**
	 * 
	 * @param supplierOrderId - String
	 */
	public void setSupplierOrderId(final String supplierOrderId) {
		this.supplierOrderId = supplierOrderId;
	}

	/**
	 * 
	 * @return String
	 */
	public String getOrderResponseDate() {
		return orderResponseDate;
	}

	/**
	 * 
	 * @param orderResponseDate - String
	 */
	public void setOrderResponseDate(final String orderResponseDate) {
		this.orderResponseDate = orderResponseDate;
	}

	/**
	 * 
	 * @return String
	 */
	public String getOrderId() {
		return orderId;
	}

	/**
	 * 
	 * @param orderId - String
	 */
	public void setOrderId(final String orderId) {
		this.orderId = orderId;
	}

	/**
	 * 
	 * @return - String
	 */
	public String getOrderDate() {
		return orderDate;
	}

	/**
	 * 
	 * @param orderDate - String
	 */
	public void setOrderDate(final String orderDate) {
		this.orderDate = orderDate;
	}

	/**
	 * 
	 * @return String
	 */
	public String getAltCustomerOrderId() {
		return altCustomerOrderId;
	}

	/**
	 * 
	 * @param altCustomerOrderId - String
	 */
	public void setAltCustomerOrderId(final String altCustomerOrderId) {
		this.altCustomerOrderId = altCustomerOrderId;
	}

	/**
	 * 
	 * @return XmlOrderPartiesReference 
	 */
	public XmlOrderPartiesReference getOrderPartiesReference() {
		return orderPartiesReference;
	}

	/**
	 * 
	 * @param orderPartiesReference - XmlOrderPartiesReference
	 */
	public void setOrderPartiesReference(final XmlOrderPartiesReference orderPartiesReference) {
		this.orderPartiesReference = orderPartiesReference;
	}

	/**
	 * 
	 * @return String
	 */
	public String getCurrency() {
		return currency;
	}

	/**
	 * 
	 * @param currency - String
	 */
	public void setCurrency(final String currency) {
		this.currency = currency;
	}

	/**
	 * 
	 * @return XmlDeliveryDate
	 */
	public XmlDeliveryDate getDeliveryDate() {
		return deliveryDate;
	}

	/**
	 * 
	 * @param deliveryDate - XmlDeliveryDate
	 */
	public void setDeliveryDate(final XmlDeliveryDate deliveryDate) {
		this.deliveryDate = deliveryDate;
	}

	/**
	 * 
	 * @return List di XmlParty
	 */
	public List<XmlParty> getParties() {
		return parties;
	}

	/**
	 * 
	 * @param parties - List di XmlParty
	 */
	public void setParties(final List<XmlParty> parties) {
		this.parties = parties;
	}

	/**
	 * 
	 * @return XmlRemarks
	 */
	public XmlRemarks getRemarks() {
		return remarks;
	}

	/**
	 * 
	 * @param remarks - XmlRemarks
	 */
	public void setRemarks(final XmlRemarks remarks) {
		this.remarks = remarks;
	}
	
	
	
	
}
