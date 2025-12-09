package com.beemediate.beemediate.domain.pojo.order;

import java.util.Arrays;

//import org.jmlspecs.annotation.CodeBigintMath;
//import org.jmlspecs.annotation.SkipEsc;

/***
 * Struttura POJO per validare le informazioni dell'Ordine di Acquisto.
 * Funge da pre-computazione per il DTO da mandare al fornitore.
 * Si basa sulla specifica XML-OpenTrans compatibile coi sistemi del fornitore. 
 * E' costituito da:
 * <ul>
 * <li>una struttura OrderHeader, contenente le informazioni rilevanti per la transazione;</li>
 * <li>un array di elementi OrderItem, ognuna delle quali contiene le informazioni riguardo un l'articolo da rifornire; </li>
 * <li>una struttura OrderSummary con informazioni sommarie relative all'ordine.</li>
 * </ul>
 * */
public class OrderStructure {
	
	//order.order_header
	/***Struttura OrderHeader con le informazioni rilevanti per la transazione*/
	private /*@ spec_public nullable @*/ OrderHeader header = null;
	//order.order_item_list
	/***Array di elementi OrderItem contenenti le informazioni riguardo gli articoli richiesti*/
	private /*@ spec_public nullable @*/ OrderItem[] itemList = null;
	//order.order_summary
	/***Struttura OrderSummary con informazioni sintetiche per l'ordine.*/
	private /*@ spec_public nullable @*/ OrderSummary orderSummary = null;
	
	/*@ public invariant itemList!=null ==> 0<itemList.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant itemList!=null ==> (\forall int i; 0<=i & i<itemList.length; itemList[i] != null); @*/
	/*@ public invariant itemList!=null ==> (\forall int i; 0<=i & i<itemList.length; \typeof(itemList[i]) == \type(OrderItem) ); @*/
	/*@ public invariant itemList!=null ==> \elemtype(\typeof(itemList)) == \type(OrderItem); @*/
	/*@ public invariant (itemList!=null & orderSummary!=null) ==> orderSummary.totalItemNum == itemList.length; @*/
	
	/**
	 * Costruttore
	 */
	//@ public normal_behaviour
	//@ ensures header == null & itemList == null & orderSummary == null;
	//@ pure
	public OrderStructure() {/*empty constructor*/}
	
	/**
	 * Copy Constructor
	 */
	//@SkipEsc
	public OrderStructure(final OrderStructure copy) {
		this.header = new OrderHeader(copy.getHeader());
		this.itemList = copy.getItemList().clone();
		this.orderSummary = new OrderSummary(copy.getOrderSummary());
	}
	
	/**
	 * 
	 * @return struttura OrderHeader
	 */
	//@ public normal_behaviour
	//@ requires header!=null;
	//@ ensures \result==header;
	//@ ensures \old(header)==header;
	public /*@ pure @*/ OrderHeader getHeader() {
		return header;
	}
	
	/**
	 * 
	 * @param header - struttura OrderHeader
	 */
	//@ public normal_behaviour
	//@ ensures this.header!=null;
	public void setHeader(/*@ non_null @*/final OrderHeader header) {
		this.header = header;
	}
	
	/**
	 * 
	 * @return Array di elementi OrderItem, specificanti gli articoli
	 */
	//@ public normal_behaviour
	//@ requires itemList!=null;
	//@ ensures \result==itemList;
	public /*@ pure @*/ OrderItem[] getItemList() {
		return itemList;
	}

	/**
	 * 
	 * @param itemList - Array di elementi OrderItem
	 */
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
	public void setItemList(/*@ non_null @*/final OrderItem[] itemList) {
		this.itemList = itemList;
	}
	
	/**
	 * 
	 * @return OrderSummary - sommario dell'ordine
	 */
	//@ public normal_behaviour
	//@ requires orderSummary != null;
	//@ ensures \result == orderSummary;
	public /*@ pure @*/ OrderSummary getOrderSummary() {
		return orderSummary;
	}

	/**
	 * 
	 * @param orderSummary - sommario dell'ordine
	 */
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
//	@CodeBigintMath
	public void setOrderSummary(/*@ non_null @*/final OrderSummary orderSummary) {
		this.orderSummary = orderSummary;
	}
	
//	@SkipEsc
	@Override
	public String toString() {
		return "OrderStructure [header=" + header + ", itemList=" + Arrays.toString(itemList) + ", orderSummary="
				+ orderSummary + "]";
	}
	
	
}
