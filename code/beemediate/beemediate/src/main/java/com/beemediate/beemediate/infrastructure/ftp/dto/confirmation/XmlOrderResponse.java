package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import java.util.List;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Conferma d'ordine
 */
@JacksonXmlRootElement(localName = "ORDERRESPONSE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlOrderResponse {
	
	/**
	 * namespace
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String xmlns = "http://www.opentrans.org/XMLSchema/2.1";
	
	/**
	 * namespace
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:xsi")
	private String xsi = "http://www.w3.org/2001/XMLSchema-instance";
	
	/**
	 * namespace
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:bmecat")
	private String bmecat = "http://www.bmecat.org/bmecat/2005";
	
	/**
	 * versione
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String version="2.1";
	
	/**
	 * Intestazione della conferma d'ordine XML
	 */
	@JacksonXmlProperty(localName="ORDERRESPONSE_HEADER")
	private XmlOrderResponseHeader orderResponseHeader;
	
	/**
	 * Elenco di conferma degli articoli dell'ordine
	 */
    @JacksonXmlElementWrapper(localName = "ORDERRESPONSE_ITEM_LIST", useWrapping = true) 
	@JacksonXmlProperty(localName="ORDERRESPONSE_ITEM")
	private List<XmlOrderResponseItem> orderResponseItemList;
	
    /**
     * Riepilogo dell'ordine
     */
	@JacksonXmlProperty(localName="ORDERRESPONSE_SUMMARY")
	private XmlOrderResponseSummary orderSummary;

	/**
	 * 
	 * @return String
	 */
	public String getXmlns() {
		return xmlns;
	}

	/**
	 * 
	 * @param xmlns String
	 */
	public void setXmlns(final String xmlns) {
		this.xmlns = xmlns;
	}

	/**
	 * 
	 * @return String
	 */
	public String getXsi() {
		return xsi;
	}

	/**
	 * 
	 * @param xsi - String
	 */
	public void setXsi(final String xsi) {
		this.xsi = xsi;
	}

	/**
	 * 
	 * @return - String
	 */
	public String getBmecat() {
		return bmecat;
	}

	/**
	 * 
	 * @param bmecat - String
	 */
	public void setBmecat(final String bmecat) {
		this.bmecat = bmecat;
	}

	/**
	 * 
	 * @return String
	 */
	public String getVersion() {
		return version;
	}

	/**
	 * 
	 * @param version - String
	 */
	public void setVersion(String version) {
		this.version = version;
	}

	/**
	 * 
	 * @return XmlOrderResponseHeader 
	 */
	public XmlOrderResponseHeader getOrderResponseHeader() {
		return orderResponseHeader;
	}

	/**
	 * 
	 * @param orderResponseHeader - XmlOrderResponseHeader
	 */
	public void setOrderResponseHeader(XmlOrderResponseHeader orderResponseHeader) {
		this.orderResponseHeader = orderResponseHeader;
	}

	/**
	 * 
	 * @return List di XmlOrderResponseItem
	 */
	public List<XmlOrderResponseItem> getOrderResponseItemList() {
		return orderResponseItemList;
	}

	/**
	 * 
	 * @param orderResponseItem - List List di XmlOrderResponseItem
	 */
	public void setOrderResponseItemList(List<XmlOrderResponseItem> orderResponseItemList) {
		this.orderResponseItemList = orderResponseItemList;
	}

	/**
	 * 
	 * @return XmlOrderResponseSummary
	 */
	public XmlOrderResponseSummary getOrderSummary() {
		return orderSummary;
	}

	/**
	 * 
	 * @param orderSummary - XmlOrderResponseSummary 
	 */
	public void setOrderSummary(XmlOrderResponseSummary orderSummary) {
		this.orderSummary = orderSummary;
	}

	
}