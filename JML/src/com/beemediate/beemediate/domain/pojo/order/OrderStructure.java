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
