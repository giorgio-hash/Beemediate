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
	@JacksonXmlProperty(isAttribute=true, localName="xmlns")
	private static final String XMLNS = "http://www.opentrans.org/XMLSchema/2.1";

	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:xsi")
	private static final String XSI = "http://www.w3.org/2001/XMLSchema-instance";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xmlns:bmecat")
	private static final String BMECAT = "http://www.bmecat.org/bmecat/2005";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="version")
	private static final String VERSION="2.1";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="type")
	private static final String TYPE="standard";
	
	/**
	 * Attributo tag ROOT del file
	 */
	@JacksonXmlProperty(isAttribute=true, localName="xsi:schemaLocation")
	private static final String SCHEMA_LOCATION = "http://www.opentrans.org/XMLSchema/2.1/opentrans_2_1.xsd";
	
	/**
	 * Riferimento a DTO XmlOrderHeader per ORDER_HEADER
	 */
	@JacksonXmlProperty(localName="ORDER_HEADER")
	public final XmlOrderHeader oh;
	
	/**
	 * Riferimento a lista di DTO XmlItem per ORDER_ITEM. Jackson crea un tag wrapper ORDER_ITEM_LIST attorno ai ORDER_ITEM
	 */
    @JacksonXmlElementWrapper(localName = "ORDER_ITEM_LIST", useWrapping = true) 
    @JacksonXmlProperty(localName = "ORDER_ITEM")  
	private final List<XmlItem> orderItem;
	
    /**
     * Riferimento a DTO XmlOrderSummary per ORDER_SUMMARY.
     */
	@JacksonXmlProperty(localName="ORDER_SUMMARY")
	public final XmlOrderSummary os;

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
		return XMLNS;
	}

	/**
	 * 
	 * @return String
	 */
	public String getXsi() {
		return XSI;
	}

	/**
	 * 
	 * @return String
	 */
	public String getBmecat() {
		return BMECAT;
	}

	/**
	 * 
	 * @return String
	 */
	public String getVersion() {
		return VERSION;
	}

	/**
	 * 
	 * @return String
	 */
	public String getType() {
		return TYPE;
	}

	/**
	 * 
	 * @return String
	 */
	public String getSchemaLocation() {
		return SCHEMA_LOCATION;
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


}