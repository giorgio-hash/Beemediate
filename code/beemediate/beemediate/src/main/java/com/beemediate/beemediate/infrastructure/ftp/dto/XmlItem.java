package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER_ITEM")
public class XmlItem {
	
	@JacksonXmlProperty(localName="LINE_ITEM_ID")
	private int lineItemId;
	
	@JacksonXmlProperty(localName="PRODUCT_ID")
	private XmlProductId prodId;
	
	@JacksonXmlProperty(localName="QUANTITY")
	private float quantity;
	
	@JacksonXmlProperty(localName="bmecat:ORDER_UNIT")
	private String orderUnit;

	
	
	
	public XmlItem(OrderItem item) {
		super();
		this.lineItemId = Integer.parseInt(item.getLineItemID());
		this.prodId = new XmlProductId(
								item.getSupplierID(),
								item.getBuyerID(),
								item.getDescriptionShort()
							);
		this.quantity = Float.parseFloat(item.getQuantity());
		this.orderUnit = item.getOrderUnit();
	}




	public int getLineItemId() {
		return lineItemId;
	}




	public XmlProductId getProdId() {
		return prodId;
	}




	public float getQuantity() {
		return quantity;
	}




	public String getOrderUnit() {
		return orderUnit;
	}


}