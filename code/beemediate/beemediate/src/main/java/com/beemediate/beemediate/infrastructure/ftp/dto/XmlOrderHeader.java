package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER_HEADER")
public class XmlOrderHeader {
	
	@JacksonXmlProperty(localName="ORDER_INFO")
	private XmlOrderInfo orderInfo;

	public XmlOrderHeader(OrderHeader head) {
		super();
		this.orderInfo = new XmlOrderInfo( head );
	}

	public XmlOrderInfo getOrderInfo() {
		return orderInfo;
	}

	
}
