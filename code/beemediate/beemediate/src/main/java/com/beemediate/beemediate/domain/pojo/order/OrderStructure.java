package com.beemediate.beemediate.domain.pojo.order;

import java.util.Arrays;

public class OrderStructure {
	
	//order.order_header
	private OrderHeader header;
	//order.order_item_list
	private OrderItem[] itemList;
	//order.order_summary
	private OrderSummary orderSummary;
	
	
	public OrderHeader getHeader() {
		return header;
	}
	public void setHeader(OrderHeader header) {
		this.header = header;
	}
	public void setItemList(OrderItem[] itemList) {
		this.itemList = itemList;
	}
	public void setOrderSummary(OrderSummary orderSummary) {
		this.orderSummary = orderSummary;
	}
	@Override
	public String toString() {
		return "OrderStructure [header=" + header + ", itemList=" + Arrays.toString(itemList) + ", orderSummary="
				+ orderSummary + "]";
	}
	
	
}
