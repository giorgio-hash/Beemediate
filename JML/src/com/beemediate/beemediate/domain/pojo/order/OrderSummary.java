package com.beemediate.beemediate.domain.pojo.order;

import org.jmlspecs.annotation.CodeBigintMath;
import org.jmlspecs.annotation.SkipEsc;

/***Parte di OrderStructure. Contiene un riepilogo dell'ordine, più precisamente il numero di OrderItem, in formato int.*/
public class OrderSummary {
	
	/***Numero totale di OrderItem nel OrderStructure.*/
	private /*@ spec_public @*/ int totalItemNum;

	/*@ public invariant 0<totalItemNum<=Integer.MAX_VALUE; @*/
	
	/***Costruttore*/
	@SkipEsc
	public OrderSummary() {/*empty constructor*/}
	
	/**
	 * Copy Constructor
	 */
	/*@ public normal_behaviour
	  @ requires copy != null;
	  @ ensures totalItemNum == copy.totalItemNum;
	  @ ensures this != copy;
	  @ ensures this != null;
	  @ ensures \not_modified(copy);
	  @*/
	public OrderSummary(OrderSummary copy) {
		this.totalItemNum = copy.totalItemNum;
	}
	
	/**
	 * 
	 * @return int - numero di OrderItem nel OrderStructure
	 */
	//@ ensures \result==totalItemNum;
	public /*@ pure @*/ int getTotalItemNum() {
		return totalItemNum;
	}

	/**
	 * 
	 * @param totalItemNum - int
	 */
	//@ requires totalItemNum>0;
	//@ ensures this.totalItemNum>0;
//	@CodeBigintMath
	public void setTotalItemNum(final int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	@SkipEsc
	@Override
	public String toString() {
		return "OrderSummary [totalItemNum=" + totalItemNum + "]";
	}

	
}
