package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlProductID;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Conferma per l'articolo dell'ordine
 */
@JacksonXmlRootElement(localName="ORDERRESPONSE_ITEM")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseItem {
	
	/**
	 * Numero d'ordine del cliente
	 */
	@JacksonXmlProperty(localName="LINE_ITEM_ID")
	private int lineItemId;
	
	/**
	 * Identificativi del prodotto
	 */
	@JacksonXmlProperty(localName="PRODUCT_ID")
	private XmlProductID productId;
	
	/**
	 * Quantità ordinata in pezzi
	 */
	@JacksonXmlProperty(localName="QUANTITY")
	private float quantity;
	
	/**
	 * Unità ISO “pezzo”
	 */
	@JacksonXmlProperty(localName="bmecat:ORDER_UNIT")
	private String orderUnit;
	
	/**
	 * Prezzo netto quantità articolo più supplementi e sconti

	 */
	@JacksonXmlProperty(localName="PRICE_LINE_AMOUNT")
	private float priceLineAmount;
	
	/**
	 * Prezzi fissi per il prodotto (tasse e prezzo base)
	 */
	@JacksonXmlProperty(localName="PRODUCT_PRICE_FIX")
	private XmlProductPriceFix productPriceFix;
	
	/**
	 * Proprietà dell'articolo
	 */
	@JacksonXmlElementWrapper(localName = "PRODUCT_FEATURES", useWrapping = true)
	@JacksonXmlProperty(localName="FEATURE")
	private List<XmlProductFeature> productFeatures;
	
	/**
	 * Data di consegna
	 */
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private XmlDeliveryDate deliveryDate;
	
	/**
	 * Numero d'ordine del fornitore
	 */
	@JacksonXmlProperty(localName="REMARKS")
	private XmlRemarks remarks;

	
	/**
	 * 
	 * @return int
	 */
	public int getLineItemId() {
		return lineItemId;
	}

	/**
	 * 
	 * @param lineItemId - int
	 */
	public void setLineItemId(final int lineItemId) {
		this.lineItemId = lineItemId;
	}

	/**
	 * 
	 * @return XmlProductID
	 */
	public XmlProductID getProductId() {
		return productId;
	}

	/**
	 * 
	 * @param productId - XmlProductID
	 */
	public void setProductId(final XmlProductID productId) {
		this.productId = productId;
	}

	/**
	 * 
	 * @return float
	 */
	public float getQuantity() {
		return quantity;
	}

	/**
	 * 
	 * @param quantity - float
	 */
	public void setQuantity(final float quantity) {
		this.quantity = quantity;
	}

	/**
	 * 
	 * @return String
	 */
	public String getOrderUnit() {
		return orderUnit;
	}

	/**
	 * 
	 * @param orderUnit - String
	 */
	public void setOrderUnit(final String orderUnit) {
		this.orderUnit = orderUnit;
	}

	/**
	 * 
	 * @return float
	 */
	public float getPriceLineAmount() {
		return priceLineAmount;
	}

	/**
	 * 
	 * @param priceLineAmount - float
	 */
	public void setPriceLineAmount(final float priceLineAmount) {
		this.priceLineAmount = priceLineAmount;
	}

	/**
	 * 
	 * @return XmlProductPriceFix
	 */
	public XmlProductPriceFix getProductPriceFix() {
		return productPriceFix;
	}

	/**
	 * 
	 * @param productPriceFix - XmlProductPriceFix
	 */
	public void setProductPriceFix(final XmlProductPriceFix productPriceFix) {
		this.productPriceFix = productPriceFix;
	}

	/**
	 * 
	 * @return List di XmlProductFeature
	 */
	public List<XmlProductFeature> getProductFeatures() {
		return productFeatures;
	}

	/**
	 * 
	 * @param productFeatures - List di XmlProductFeature
	 */
	public void setProductFeatures(final  List<XmlProductFeature> productFeatures) {
		this.productFeatures = productFeatures;
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