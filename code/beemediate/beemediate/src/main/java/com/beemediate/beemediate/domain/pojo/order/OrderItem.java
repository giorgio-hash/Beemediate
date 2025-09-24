package com.beemediate.beemediate.domain.pojo.order;

public class OrderItem {
	
	
	private String lineItemID;
	private String quantity;
	private String orderUnit;
	
	//order_item.product_id
	private String supplierID;
	private String buyerID;
	private String descriptionShort;
	
	public String getLineItemID() {
		return lineItemID;
	}
	public void setLineItemID(String lineItemID) {
		this.lineItemID = lineItemID;
	}
	public String getQuantity() {
		return quantity;
	}
	public void setQuantity(String quantity) {
		this.quantity = quantity;
	}
	public String getOrderUnit() {
		return orderUnit;
	}
	public void setOrderUnit(String orderUnit) {
		this.orderUnit = orderUnit;
	}
	public String getSupplierID() {
		return supplierID;
	}
	public String getBuyerID() {
		return buyerID;
	}
	public String getDescriptionShort() {
		return descriptionShort;
	}
	public void setSupplierID(String supplierID) {
		this.supplierID = supplierID;
	}
	public void setBuyerID(String buyerID) {
		this.buyerID = buyerID;
	}
	public void setDescriptionShort(String descriptionShort) {
		this.descriptionShort = descriptionShort;
	}
	
	@Override
	public String toString() {
		return "OrderItem [lineItemID=" + lineItemID + ", quantity=" + quantity + ", orderUnit=" + orderUnit
				+ ", supplierID=" + supplierID + ", buyerID=" + buyerID + ", descriptionShort=" + descriptionShort
				+ "]";
	}
	
	

}
