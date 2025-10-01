package com.beemediate.beemediate.domain.pojo.order;

//import org.jmlspecs.annotation.SkipEsc;

public class OrderItem {
	
	
	private /*@ spec_public @*/ String lineItemID = "";
	private /*@ spec_public @*/ String quantity = "";
	private /*@ spec_public @*/ String orderUnit = "";
	
	//order_item.product_id
	private /*@ spec_public @*/ String supplierID = "";
	private /*@ spec_public @*/ String buyerID = "";
	private /*@ spec_public @*/ String descriptionShort = "";
	
	//@ public normal_behaviour
	/*@ ensures lineItemID!=null & quantity!=null & orderUnit!=null
	  @			& supplierID!=null & buyerID!=null & descriptionShort!=null;
	  @ pure
	  @*/
	public OrderItem() {}
	
	//@ public normal_behaviour
	//@ ensures \result==lineItemID;
	public /*@ pure @*/ String getLineItemID() {
		return lineItemID;
	}
	
	//@ public normal_behaviour
	//@ ensures this.lineItemID!=null;
	public void setLineItemID(/*@ non_null @*/ String lineItemID) {
		this.lineItemID = lineItemID;
	}
	
	//@ public normal_behaviour
	//@ ensures \result==quantity;
	public /*@ pure @*/ String getQuantity() {
		return quantity;
	}
	
	//@ public normal_behaviour
	//@ ensures this.quantity!=null;
	public void setQuantity(/*@ non_null @*/ String quantity) {
		this.quantity = quantity;
	}
	
	//@ public normal_behaviour
	//@ ensures \result==orderUnit;
	public /*@ pure @*/ String getOrderUnit() {
		return orderUnit;
	}
	
	//@ public normal_behaviour
	//@ ensures this.orderUnit!=null;
	public void setOrderUnit(/*@ non_null @*/ String orderUnit) {
		this.orderUnit = orderUnit;
	}
	
	//@ public normal_behaviour
	//@ ensures \result==supplierID;
	public /*@ pure @*/ String getSupplierID() {
		return supplierID;
	}
	
	//@ public normal_behaviour
	//@ ensures \result==buyerID;
	public String getBuyerID() {
		return buyerID;
	}
	
	//@ public normal_behaviour
	//@ ensures \result==descriptionShort;
	public /*@ pure @*/ String getDescriptionShort() {
		return descriptionShort;
	}
	
	//@ public normal_behaviour
	//@ ensures this.supplierID!=null;
	public void setSupplierID(/*@ non_null @*/ String supplierID) {
		this.supplierID = supplierID;
	}
	
	//@ public normal_behaviour
	//@ ensures this.buyerID!=null;
	public void setBuyerID(/*@ non_null @*/ String buyerID) {
		this.buyerID = buyerID;
	}
	
	//@ public normal_behaviour
	//@ ensures this.descriptionShort!=null;
	public void setDescriptionShort(/*@ non_null @*/ String descriptionShort) {
		this.descriptionShort = descriptionShort;
	}
	
//	@SkipEsc
	@Override
	public String toString() {
		return "OrderItem [lineItemID=" + lineItemID + ", quantity=" + quantity + ", orderUnit=" + orderUnit
				+ ", supplierID=" + supplierID + ", buyerID=" + buyerID + ", descriptionShort=" + descriptionShort
				+ "]";
	}
	
	

}
