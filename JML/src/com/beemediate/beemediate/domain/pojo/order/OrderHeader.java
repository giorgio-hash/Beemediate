package com.beemediate.beemediate.domain.pojo.order;

import org.jmlspecs.annotation.SkipEsc;

public class OrderHeader {
	
	//order_info
	private /*@ spec_public @*/ String orderID = "";
	private /*@ spec_public @*/ String orderDate = "";
	private /*@ spec_public @*/ String currency = "";
	
	//order_info.parties.party[party_role="buyer"]
	private /*@ spec_public @*/ String buyerID = "";
	//order_info.parties.party[party_role="supplier"]
	private /*@ spec_public @*/ String supplierID = "";
	//order_info.parties.party[party_role="delivery"]
	private /*@ spec_public @*/ String deliveryID = "";
	
	//order_info.delivery_date
	private /*@ spec_public @*/ String startDate = "";
	private /*@ spec_public @*/ String endDate = "";
	
	//order_info.order_parties_reference
	private /*@ spec_public @*/ String buyerIDRef = "";
	private /*@ spec_public @*/ String supplierIDRef = "";
	
	//order_info.parties_reference.shipment_parties_reference
	private /*@ spec_public @*/ String deliveryIDRef = "";
	
	/*@ ensures buyerID!=null & supplierID!=null & deliveryID!=null
	  @			& startDate!=null & endDate!=null
	  @			& buyerIDRef!=null & supplierIDRef!=null
	  @			& deliveryIDRef!=null;
	  @*/
	//@ pure
	public OrderHeader() {};
	
	//@ public normal_behaviour
	//@ ensures \result == orderID;
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

	//@ public normal_behaviour
	//@ ensures this.orderID!=null;
	public void setOrderID( /*@ non_null @*/ String orderID) {
		this.orderID = orderID;
	}

	//@ public normal_behaviour
	//@ ensures \result==orderDate;
	public /*@ pure @*/  String getOrderDate() {
		return orderDate;
	}

	//@ public normal_behaviour
	//@ ensures this.orderDate!=null;
	public void setOrderDate( /*@ non_null @*/ String orderDate) {
		this.orderDate = orderDate;
	}

	//@ public normal_behaviour
	//@ ensures \result==currency;
	public /*@ pure @*/  String getCurrency() {
		return currency;
	}

	//@ public normal_behaviour
	//@ ensures this.currency!=null;
	public void setCurrency( /*@ non_null @*/ String currency) {
		this.currency = currency;
	}

	//@ public normal_behaviour
	//@ ensures \result==buyerID;
	public /*@ pure @*/  String getBuyerID() {
		return buyerID;
	}

	//@ public normal_behaviour
	//@ ensures this.buyerID!=null;
	public void setBuyerID( /*@ non_null @*/ String buyerID) {
		this.buyerID = buyerID;
	}

	//@ public normal_behaviour
	//@ ensures \result==supplierID;
	public /*@ pure @*/ String getSupplierID() {
		return supplierID;
	}

	//@ public normal_behaviour
	//@ ensures this.supplierID!=null;
	public void setSupplierID( /*@ non_null @*/ String supplierID) {
		this.supplierID = supplierID;
	}

	//@ public normal_behaviour
	//@ ensures \result==deliveryID;
	public /*@ pure @*/ String getDeliveryID() {
		return deliveryID;
	}

	//@ public normal_behaviour
	//@ ensures this.deliveryID==deliveryID;
	public void setDeliveryID( /*@ non_null @*/ String deliveryID) {
		this.deliveryID = deliveryID;
	}

	//@ public normal_behaviour
	//@ ensures \result==startDate;
	public /*@ pure @*/ String getStartDate() {
		return startDate;
	}

	//@ public normal_behaviour
	//@ ensures this.startDate!=null;
	public void setStartDate( /*@ non_null @*/ String startDate) {
		this.startDate = startDate;
	}

	//@ public normal_behaviour
	//@ ensures \result == endDate;
	public /*@ pure @*/ String getEndDate() {
		return endDate;
	}

	//@ public normal_behaviour
	//@ ensures this.endDate!=null;
	public void setEndDate(/*@ non_null @*/ String endDate) {
		this.endDate = endDate;
	}

	//@ public normal_behaviour
	//@ ensures \result==buyerIDRef;
	public /*@ pure @*/ String getBuyerIDRef() {
		return buyerIDRef;
	}

	//@ public normal_behaviour
	//@ ensures this.buyerIDRef!=null; 
	public void setBuyerIDRef(/*@ non_null @*/ String buyerIDRef) {
		this.buyerIDRef = buyerIDRef;
	}

	//@ public normal_behaviour
	//@ ensures \result==supplierIDRef;
	public /*@ pure @*/ String getSupplierIDRef() {
		return supplierIDRef;
	}

	//@ public normal_behaviour
	//@ ensures this.supplierIDRef!=null;
	public void setSupplierIDRef(/*@ non_null @*/ String supplierIDRef) {
		this.supplierIDRef = supplierIDRef;
	}

	//@ public normal_behaviour
	//@ ensures \result==deliveryIDRef;
	public /*@ pure @*/ String getDeliveryIDRef() {
		return deliveryIDRef;
	}

	//@ public normal_behaviour
	//@ ensures this.deliveryIDRef!=null;
	public void setDeliveryIDRef(/*@ non_null @*/ String deliveryIDRef) {
		this.deliveryIDRef = deliveryIDRef;
	}

	@SkipEsc
	@Override
	public String toString() {
		return "OrderHeader [orderID=" + orderID + ", orderDate=" + orderDate + ", currency=" + currency + ", buyerID="
				+ buyerID + ", supplierID=" + supplierID + ", deliveryID=" + deliveryID + ", startDate=" + startDate
				+ ", endDate=" + endDate + ", buyerIDRef=" + buyerIDRef + ", supplierIDRef=" + supplierIDRef
				+ ", deliveryIDRef=" + deliveryIDRef + "]";
	}

	
	
}
