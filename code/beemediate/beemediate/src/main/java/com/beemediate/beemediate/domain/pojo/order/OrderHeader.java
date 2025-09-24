package com.beemediate.beemediate.domain.pojo.order;

public class OrderHeader {
	
	//order_info
	private String orderID;
	private String orderDate;
	private String currency;
	
	//order_info.parties.party[party_role="buyer"]
	private String buyerID;
	//order_info.parties.party[party_role="supplier"]
	private String supplierID;
	//order_info.parties.party[party_role="delivery"]
	private String deliveryID;
	
	//order_info.delivery_date
	private String startDate;
	private String endDate;
	
	//order_info.order_parties_reference
	private String buyerIDRef;
	private String supplierIDRef;
	
	//order_info.parties_reference.shipment_parties_reference
	private String deliveryIDRef;

	
	
	public String getOrderID() {
		return orderID;
	}

	public void setOrderID(String orderID) {
		this.orderID = orderID;
	}

	public String getOrderDate() {
		return orderDate;
	}

	public void setOrderDate(String orderDate) {
		this.orderDate = orderDate;
	}

	public String getCurrency() {
		return currency;
	}

	public void setCurrency(String currency) {
		this.currency = currency;
	}

	public String getBuyerID() {
		return buyerID;
	}

	public void setBuyerID(String buyerID) {
		this.buyerID = buyerID;
	}

	public String getSupplierID() {
		return supplierID;
	}

	public void setSupplierID(String supplierID) {
		this.supplierID = supplierID;
	}

	public String getDeliveryID() {
		return deliveryID;
	}

	public void setDeliveryID(String deliveryID) {
		this.deliveryID = deliveryID;
	}

	public String getStartDate() {
		return startDate;
	}

	public void setStartDate(String startDate) {
		this.startDate = startDate;
	}

	public String getEndDate() {
		return endDate;
	}

	public void setEndDate(String endDate) {
		this.endDate = endDate;
	}

	public String getBuyerIDRef() {
		return buyerIDRef;
	}

	public void setBuyerIDRef(String buyerIDRef) {
		this.buyerIDRef = buyerIDRef;
	}

	public String getSupplierIDRef() {
		return supplierIDRef;
	}

	public void setSupplierIDRef(String supplierIDRef) {
		this.supplierIDRef = supplierIDRef;
	}

	public String getDeliveryIDRef() {
		return deliveryIDRef;
	}

	public void setDeliveryIDRef(String deliveryIDRef) {
		this.deliveryIDRef = deliveryIDRef;
	}

	@Override
	public String toString() {
		return "OrderHeader [orderID=" + orderID + ", orderDate=" + orderDate + ", currency=" + currency + ", buyerID="
				+ buyerID + ", supplierID=" + supplierID + ", deliveryID=" + deliveryID + ", startDate=" + startDate
				+ ", endDate=" + endDate + ", buyerIDRef=" + buyerIDRef + ", supplierIDRef=" + supplierIDRef
				+ ", deliveryIDRef=" + deliveryIDRef + "]";
	}

	
	
}
