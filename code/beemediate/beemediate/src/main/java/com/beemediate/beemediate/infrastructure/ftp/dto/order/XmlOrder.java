package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import java.util.List;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans dell'ordine.
 */
@JacksonXmlRootElement(localName = "ORDER")
public class XmlOrder {
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String xmlns = "http://www.opentrans.org/XMLSchema/2.1";

	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:xsi")
	private String xsi = "http://www.w3.org/2001/XMLSchema-instance";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:bmecat")
	private String bmecat = "http://www.bmecat.org/bmecat/2005";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String version="2.1";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true)
	private String type="standard";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xsi:schemaLocation")
	private String schemaLocation = "http://www.opentrans.org/XMLSchema/2.1/opentrans_2_1.xsd";
	
	/**
	 * Riferimento a DTO XmlOrderHeader per ORDER_HEADER
	 */
	@JacksonXmlProperty(localName="ORDER_HEADER")
	public XmlOrderHeader oh;
	
	/**
	 * Riferimento a lista di DTO XmlItem per ORDER_ITEM. Jackson crea un tag wrapper ORDER_ITEM_LIST attorno ai ORDER_ITEM
	 */
    @JacksonXmlElementWrapper(localName = "ORDER_ITEM_LIST", useWrapping = true) 
    @JacksonXmlProperty(localName = "ORDER_ITEM")  
	private List<XmlItem> orderItem;
	
    /**
     * Riferimento a DTO XmlOrderSummary per ORDER_SUMMARY.
     */
	@JacksonXmlProperty(localName="ORDER_SUMMARY")
	public XmlOrderSummary os;

	/**
	 * Empty constructor for deserializer
	 */
	public XmlOrder() {/*empty constructor for deserializer*/}
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans dell'ordine. Crea la radice del documento contenente attributi relativi al namespace.
	 * <br>La struttura dell'ordine è formata da tre elementi principali:
	 * <ul>
	 * <li>Una struttura ORDER_HEADER</li>
	 * <li>Una struttura ORDER_ITEM_LIST contenente una collezione di strutture ORDER_ITEM</li>
	 * <li>Una struttura ORDER_SUMMARY</li>
	 * </ul>
	 * @param oh - {@code XmlOrderHeader} per creare struttura XML-OpenTrans ORDER_HEADER
	 * @param orderItem - {@code List<XmlItem>} per creare le strutture XML-OpenTrans ORDER_ITEM nel tag ORDER_ITEM_LIST
	 * @param os - {@code XmlOrderSummary} per creare struttura XML-OpenTrans ORDER_SUMMARY
	 */
	public XmlOrder(final XmlOrderHeader oh, final List<XmlItem> orderItem, final XmlOrderSummary os) {
		super();
		this.oh = oh;
		this.orderItem = orderItem;
		this.os = os;
	}

	/**
	 * 
	 * @return String
	 */
	public String getXmlns() {
		return xmlns;
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
	 * @return String
	 */
	public String getBmecat() {
		return bmecat;
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
	 * @return String
	 */
	public String getType() {
		return type;
	}

	/**
	 * 
	 * @return String
	 */
	public String getSchemaLocation() {
		return schemaLocation;
	}

	/**
	 * 
	 * @return String
	 */
	public XmlOrderHeader getOh() {
		return oh;
	}

	/**
	 * 
	 * @return {@code List<XmlItem>}
	 */
	public List<XmlItem> getOrderItem() {
		return orderItem;
	}

	/**
	 * 
	 * @return XmlOrderSummary
	 */
	public XmlOrderSummary getOs() {
		return os;
	}

	public void setXmlns(String xmlns) {
		this.xmlns = xmlns;
	}

	public void setXsi(String xsi) {
		this.xsi = xsi;
	}

	public void setBmecat(String bmecat) {
		this.bmecat = bmecat;
	}

	public void setVersion(String version) {
		this.version = version;
	}

	public void setType(String type) {
		this.type = type;
	}

	public void setSchemaLocation(String schemaLocation) {
		this.schemaLocation = schemaLocation;
	}

	public void setOh(XmlOrderHeader oh) {
		this.oh = oh;
	}

	public void setOrderItem(List<XmlItem> orderItem) {
		this.orderItem = orderItem;
	}

	public void setOs(XmlOrderSummary os) {
		this.os = os;
	}


}