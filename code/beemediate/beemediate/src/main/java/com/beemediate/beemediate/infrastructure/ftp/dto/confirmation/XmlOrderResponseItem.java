package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlProductID;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName="ORDERRESPONSE_ITEM")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseItem {
	
	@JacksonXmlProperty(localName="LINE_ITEM_ID")
	private int lineItemId;
	
	@JacksonXmlProperty(localName="PRODUCT_ID")
	private XmlProductID productId;
	
	@JacksonXmlProperty(localName="QUANTITY")
	private float quantity;
	
	@JacksonXmlProperty(localName="bmecat:ORDER_UNIT")
	private String orderUnit;
	
	@JacksonXmlProperty(localName="PRICE_LINE_AMOUNT")
	private float priceLineAmount;
	
	@JacksonXmlProperty(localName="PRODUCT_PRICE_FIX")
	private XmlProductPriceFix productPriceFix;
	
	@JacksonXmlElementWrapper(localName = "PRODUCT_FEATURES", useWrapping = true)
	@JacksonXmlProperty(localName="FEATURE")
	private List<XmlProductFeature> productFeatures;
	
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private XmlDeliveryDate deliveryDate;
	
	@JacksonXmlProperty(localName="REMARKS")
	private XmlRemarks remarks;

	public int getLineItemId() {
		return lineItemId;
	}

	public void setLineItemId(int lineItemId) {
		this.lineItemId = lineItemId;
	}

	public XmlProductID getProductId() {
		return productId;
	}

	public void setProductId(XmlProductID productId) {
		this.productId = productId;
	}

	public float getQuantity() {
		return quantity;
	}

	public void setQuantity(float quantity) {
		this.quantity = quantity;
	}

	public String getOrderUnit() {
		return orderUnit;
	}

	public void setOrderUnit(String orderUnit) {
		this.orderUnit = orderUnit;
	}

	public float getPriceLineAmount() {
		return priceLineAmount;
	}

	public void setPriceLineAmount(float priceLineAmount) {
		this.priceLineAmount = priceLineAmount;
	}

	public XmlProductPriceFix getProductPriceFix() {
		return productPriceFix;
	}

	public void setProductPriceFix(XmlProductPriceFix productPriceFix) {
		this.productPriceFix = productPriceFix;
	}

	public List<XmlProductFeature> getProductFeatures() {
		return productFeatures;
	}

	public void setProductFeatures(List<XmlProductFeature> productFeatures) {
		this.productFeatures = productFeatures;
	}

	public XmlDeliveryDate getDeliveryDate() {
		return deliveryDate;
	}

	public void setDeliveryDate(XmlDeliveryDate deliveryDate) {
		this.deliveryDate = deliveryDate;
	}

	public XmlRemarks getRemarks() {
		return remarks;
	}

	public void setRemarks(XmlRemarks remarks) {
		this.remarks = remarks;
	}

	

}