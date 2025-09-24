package com.beemediate.beemediate.domain.pojo.order;

public class OrderSummary {
	
	private int totalItemNum;

	public int getTotalItemNum() {
		return totalItemNum;
	}

	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	@Override
	public String toString() {
		return "OrderSummary [totalItemNum=" + totalItemNum + "]";
	}

	
}
