package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.domain.pojo.order.OrderSummary;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER_SUMMARY")
public class XmlOrderSummary {
	
	@JacksonXmlProperty(localName="TOTAL_ITEM_NUM")
	private int totalItemNum;
	

	public XmlOrderSummary(OrderSummary summary) {
		this.totalItemNum = summary.getTotalItemNum();
	}
	
	public int getTotalItemNum() {
		return totalItemNum;
	}
	
	
}
