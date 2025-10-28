package com.beemediate.beemediate.domain.pojo.order;

import java.util.Arrays;

import org.jmlspecs.annotation.CodeBigintMath;
import org.jmlspecs.annotation.SkipEsc;

public class OrderStructure {
	
	//order.order_header
	private /*@ spec_public nullable @*/ OrderHeader header = null;
	//order.order_item_list
	private /*@ spec_public nullable @*/ OrderItem[] itemList = null;
	//order.order_summary
	private /*@ spec_public nullable @*/ OrderSummary orderSummary = null;
	
	/*@ public invariant itemList!=null ==> 0<itemList.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant itemList!=null ==> (\forall int i; 0<=i & i<itemList.length; itemList[i] != null); @*/
	/*@ public invariant itemList!=null ==> (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) ); @*/
	/*@ public invariant itemList!=null ==> \elemtype(\typeof(itemList)) == \type(OrderItem); @*/
	/*@ public invariant (itemList!=null & orderSummary!=null) ==> orderSummary.totalItemNum == itemList.length; @*/
	
	//@ public normal_behaviour
	//@ ensures header == null & itemList == null & orderSummary == null;
	//@ pure
	private OrderStructure() {};
	
	/**
	 * Copy Constructor
	 */
	/*@
	  @ public normal_behaviour
	  @ requires copy!=null & copy.header!=null & copy.itemList!=null & copy.orderSummary!=null;
	  @ requires copy.itemList.length>0 
	  				& (\forall int i; 0 <= i & i < copy.itemList.length; copy.itemList[i] != null)
	  				& (\forall int i; 0<=i & i<copy.itemList.length; \typeof(copy.itemList[i]) == \type(OrderItem) )
	  				& \elemtype(\typeof(copy.itemList)) == \type(OrderItem)
	  				& copy.orderSummary.totalItemNum == copy.itemList.length;
	  @ ensures this.header!=null & this.itemList!=null & this.orderSummary!=null;
	  @ ensures itemList.length>0 
	  				& (\forall int i; 0 <= i & i < itemList.length; itemList[i] != null)
	  				& (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) )
	  				& \elemtype(\typeof(itemList)) == \type(OrderItem)
	  				& orderSummary.totalItemNum == itemList.length;
	  @ ensures this != copy;
	  @ ensures \not_modified(copy);
	  @*/
	@CodeBigintMath
	public /*@ pure @*/ OrderStructure(OrderStructure copy) {
		this.header = new OrderHeader(copy.getHeader());
		this.itemList = copy.getItemList().clone();
		//@ assume itemList.length>0;
		//@ assume (\forall int i; 0 <= i & i < itemList.length; itemList[i] != null);
		//@ assume (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) );
		//@ assume \elemtype(\typeof(itemList)) == \type(OrderItem);
		//@ assume copy.orderSummary.totalItemNum == itemList.length;
		this.orderSummary = new OrderSummary(copy.getOrderSummary());
	}
	
	//@ public normal_behaviour
	//@ requires header!=null;
	//@ ensures \result==header;
	//@ ensures \old(header)==header;
	public /*@ pure @*/ OrderHeader getHeader() {
		return header;
	}
	
	//@ public normal_behaviour
	//@ ensures this.header!=null;
	public void setHeader(/*@ non_null @*/ OrderHeader header) {
		this.header = header;
	}
	
	//@ public normal_behaviour
	//@ requires itemList!=null;
	//@ ensures \result==itemList;
	public /*@ pure @*/ OrderItem[] getItemList() {
		return itemList;
	}

	//@ public normal_behaviour
	//@ assigns this.itemList;
	//@ requires itemList.length>0;
	//@ requires (\forall int i; 0<=i & i<itemList.length; itemList[i] != null);
	//@ requires (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) );
	//@ requires \elemtype(\typeof(itemList)) == \type(OrderItem);
	//@ requires this.orderSummary!=null;
	//@ requires this.orderSummary.totalItemNum == itemList.length; 
	//@ ensures this.itemList!=null;
	//@ ensures this.itemList == itemList;
	//@
	//@ also public normal_behaviour
	//@ assigns this.itemList;
	//@ requires itemList.length>0;
	//@ requires (\forall int i; 0<=i & i<itemList.length; itemList[i] != null);
	//@ requires (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) );
	//@ requires \elemtype(\typeof(itemList)) == \type(OrderItem);
	//@ requires orderSummary == null;
	//@ ensures this.itemList!=null;
	//@ ensures this.itemList == itemList;
	public void setItemList(/*@ non_null @*/ OrderItem[] itemList) {
		this.itemList = itemList;
	}
	
	//@ public normal_behaviour
	//@ requires orderSummary != null;
	//@ ensures \result == orderSummary;
	public /*@ pure @*/ OrderSummary getOrderSummary() {
		return orderSummary;
	}

	//@ public normal_behaviour
	//@ assigns this.orderSummary;
	//@ requires itemList!=null;
	//@ requires itemList.length == orderSummary.totalItemNum;
	//@ ensures this.orderSummary!=null;
	//@ ensures this.orderSummary == orderSummary;
	//@
	//@ also public normal_behaviour
	//@ assigns this.orderSummary;
	//@ requires itemList==null;
	//@ ensures this.orderSummary!=null;
	//@ ensures this.orderSummary == orderSummary;
	@CodeBigintMath
	public void setOrderSummary(/*@ non_null @*/ OrderSummary orderSummary) {
		this.orderSummary = orderSummary;
	}
	
	@SkipEsc
	@Override
	public String toString() {
		return "OrderStructure [header=" + header + ", itemList=" + Arrays.toString(itemList) + ", orderSummary="
				+ orderSummary + "]";
	}
	
	
}
