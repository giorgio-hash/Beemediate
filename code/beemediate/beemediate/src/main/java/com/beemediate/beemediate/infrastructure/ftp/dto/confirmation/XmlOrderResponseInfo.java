package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.beemediate.beemediate.infrastructure.ftp.dto.order.XmlOrderPartiesReference;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

@JacksonXmlRootElement(localName = "ORDERRESPONSE_INFO")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseInfo {
	
	
	@JacksonXmlProperty(localName="SUPPLIER_ORDER_ID")
	private String supplierOrderId;
	
	@JacksonXmlProperty(localName="ORDERRESPONSE_DATE")
	private String orderResponseDate;
	
	@JacksonXmlProperty(localName="ORDER_ID")
	private String orderId;
	
	@JacksonXmlProperty(localName="ORDER_DATE")
	private String orderDate;
	
	@JacksonXmlProperty(localName="ALT_CUSTOMER_ORDER_ID")
	private String altCustomerOrderId;
	
	@JacksonXmlProperty(localName="ORDER_PARTIES_REFERENCE")
	private XmlOrderPartiesReference orderPartiesReference;
	
	@JacksonXmlProperty(localName="bmecat:CURRENCY")
	private String currency;
	
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private XmlDeliveryDate deliveryDate;
	
    @JacksonXmlElementWrapper(localName = "PARTIES", useWrapping = true) 
    @JacksonXmlProperty(localName = "PARTY")
	private List<XmlParty> parties;
	
	@JacksonXmlProperty(localName="REMARKS")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlRemarks remarks;

	public String getSupplierOrderId() {
		return supplierOrderId;
	}

	public void setSupplierOrderId(String supplierOrderId) {
		this.supplierOrderId = supplierOrderId;
	}

	public String getOrderResponseDate() {
		return orderResponseDate;
	}

	public void setOrderResponseDate(String orderResponseDate) {
		this.orderResponseDate = orderResponseDate;
	}

	public String getOrderId() {
		return orderId;
	}

	public void setOrderId(String orderId) {
		this.orderId = orderId;
	}

	public String getOrderDate() {
		return orderDate;
	}

	public void setOrderDate(String orderDate) {
		this.orderDate = orderDate;
	}

	public String getAltCustomerOrderId() {
		return altCustomerOrderId;
	}

	public void setAltCustomerOrderId(String altCustomerOrderId) {
		this.altCustomerOrderId = altCustomerOrderId;
	}

	public XmlOrderPartiesReference getOrderPartiesReference() {
		return orderPartiesReference;
	}

	public void setOrderPartiesReference(XmlOrderPartiesReference orderPartiesReference) {
		this.orderPartiesReference = orderPartiesReference;
	}

	public String getCurrency() {
		return currency;
	}

	public void setCurrency(String currency) {
		this.currency = currency;
	}

	public XmlDeliveryDate getDeliveryDate() {
		return deliveryDate;
	}

	public void setDeliveryDate(XmlDeliveryDate deliveryDate) {
		this.deliveryDate = deliveryDate;
	}

	public List<XmlParty> getParties() {
		return parties;
	}

	public void setParties(List<XmlParty> parties) {
		this.parties = parties;
	}

	public XmlRemarks getRemarks() {
		return remarks;
	}

	public void setRemarks(XmlRemarks remarks) {
		this.remarks = remarks;
	}
	
	
	
	
}
