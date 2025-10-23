package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDERRESPONSE_HEADER")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponseHeader {
	
	@JacksonXmlProperty(localName="CONTROL_INFO")
	private XmlControlInfo controlInfo;
	
	@JacksonXmlProperty(localName="ORDERRESPONSE_INFO")
	private XmlOrderResponseInfo orderResponseInfo;

	public XmlControlInfo getControlInfo() {
		return controlInfo;
	}

	public void setControlInfo(XmlControlInfo controlInfo) {
		this.controlInfo = controlInfo;
	}

	public XmlOrderResponseInfo getOrderResponseInfo() {
		return orderResponseInfo;
	}

	public void setOrderResponseInfo(XmlOrderResponseInfo orderResponseInfo) {
		this.orderResponseInfo = orderResponseInfo;
	}

}
