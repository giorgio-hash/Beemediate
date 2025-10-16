package com.beemediate.beemediate.infrastructure.ftp.dto;

import java.util.List;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER")
public class XmlOrder {
	
	@JacksonXmlProperty(isAttribute=true)
	private final String xmlns = "http://www.opentrans.org/XMLSchema/2.1";
	
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:xsi")
	private final String xsi = "http://www.w3.org/2001/XMLSchema-instance";
	
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:bmecat")
	private final String bmecat = "http://www.bmecat.org/bmecat/2005";
	
	@JacksonXmlProperty(isAttribute=true)
	private final String version="2.1";
	
	@JacksonXmlProperty(isAttribute=true)
	private final String type="standard";
	
	@JacksonXmlProperty(isAttribute=true, localName="xsi:schemaLocation")
	private final String schemaLocation = "http://www.opentrans.org/XMLSchema/2.1/opentrans_2_1.xsd";
	

	@JacksonXmlProperty(localName="ORDER_HEADER")
	public XmlOrderHeader oh;
	
    @JacksonXmlElementWrapper(localName = "ORDER_ITEM_LIST", useWrapping = true) 
    @JacksonXmlProperty(localName = "ORDER_ITEM")  
	private List<XmlItem> orderItem;
	
	@JacksonXmlProperty(localName="ORDER_SUMMARY")
	public XmlOrderSummary os;

	public XmlOrder(XmlOrderHeader oh, List<XmlItem> orderItem, XmlOrderSummary os) {
		super();
		this.oh = oh;
		this.orderItem = orderItem;
		this.os = os;
	}

	public String getXmlns() {
		return xmlns;
	}

	public String getXsi() {
		return xsi;
	}

	public String getBmecat() {
		return bmecat;
	}

	public String getVersion() {
		return version;
	}

	public String getType() {
		return type;
	}

	public String getSchemaLocation() {
		return schemaLocation;
	}

	public XmlOrderHeader getOh() {
		return oh;
	}

	public List<XmlItem> getOrderItem() {
		return orderItem;
	}

	public XmlOrderSummary getOs() {
		return os;
	}


}