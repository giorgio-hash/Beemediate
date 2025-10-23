package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDERRESPONSE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponse {
	
	@JacksonXmlProperty(isAttribute=true)
	private String xmlns = "http://www.opentrans.org/XMLSchema/2.1";
	
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:xsi")
	private String xsi = "http://www.w3.org/2001/XMLSchema-instance";
	
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:bmecat")
	private String bmecat = "http://www.bmecat.org/bmecat/2005";
	
	@JacksonXmlProperty(isAttribute=true)
	private String version="2.1";
	
	@JacksonXmlProperty(localName="ORDERRESPONSE_HEADER")
	private XmlOrderResponseHeader orderResponseHeader;
	
    @JacksonXmlElementWrapper(localName = "ORDERRESPONSE_ITEM_LIST", useWrapping = true) 
	@JacksonXmlProperty(localName="ORDERRESPONSE_ITEM")
	private List<XmlOrderResponseItem> orderResponseItemList;
	
	@JacksonXmlProperty(localName="ORDERRESPONSE_SUMMARY")
	private XmlOrderResponseSummary orderSummary;

	public String getXmlns() {
		return xmlns;
	}

	public void setXmlns(String xmlns) {
		this.xmlns = xmlns;
	}

	public String getXsi() {
		return xsi;
	}

	public void setXsi(String xsi) {
		this.xsi = xsi;
	}

	public String getBmecat() {
		return bmecat;
	}

	public void setBmecat(String bmecat) {
		this.bmecat = bmecat;
	}

	public String getVersion() {
		return version;
	}

	public void setVersion(String version) {
		this.version = version;
	}

	public XmlOrderResponseHeader getOrderResponseHeader() {
		return orderResponseHeader;
	}

	public void setOrderResponseHeader(XmlOrderResponseHeader orderResponseHeader) {
		this.orderResponseHeader = orderResponseHeader;
	}

	public List<XmlOrderResponseItem> getOrderResponseItemList() {
		return orderResponseItemList;
	}

	public void setOrderResponseItemList(List<XmlOrderResponseItem> orderResponseItemList) {
		this.orderResponseItemList = orderResponseItemList;
	}

	public XmlOrderResponseSummary getOrderSummary() {
		return orderSummary;
	}

	public void setOrderSummary(XmlOrderResponseSummary orderSummary) {
		this.orderSummary = orderSummary;
	}

	
}