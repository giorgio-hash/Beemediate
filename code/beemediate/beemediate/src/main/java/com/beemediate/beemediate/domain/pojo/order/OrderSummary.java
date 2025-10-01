package com.beemediate.beemediate.domain.pojo.order;

//import org.jmlspecs.annotation.CodeBigintMath;
//import org.jmlspecs.annotation.SkipEsc;

public class OrderSummary {
	
	private /*@ spec_public @*/ int totalItemNum;

	/*@ public invariant 0<totalItemNum<=Integer.MAX_VALUE; @*/
	
//	@SkipEsc
	public OrderSummary() {}
	
	//@ ensures \result==totalItemNum;
	public /*@ pure @*/ int getTotalItemNum() {
		return totalItemNum;
	}

	//@ requires totalItemNum>0;
	//@ ensures this.totalItemNum>0;
//	@CodeBigintMath
	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

//	@SkipEsc
	@Override
	public String toString() {
		return "OrderSummary [totalItemNum=" + totalItemNum + "]";
	}

	
}
