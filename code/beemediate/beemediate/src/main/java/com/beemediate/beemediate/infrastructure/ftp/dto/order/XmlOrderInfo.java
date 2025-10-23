package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.PartyType;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate.DeliveryDateType;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlPartyID;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per struttura informazioni del header ordine.
 */
@JacksonXmlRootElement(localName = "ORDER_INFO")
public class XmlOrderInfo {
	
	/**
	 * tag per numero d'ordine del cliente (35 cifre; (alfanumerico / numerico))
	 */
	@JacksonXmlProperty(localName="ORDER_ID")
	private final String orderId;
	
	/**
	 * tag per data dell'ordine
	 */
	@JacksonXmlProperty(localName="ORDER_DATE")
	private final String orderDate;
	
	/**
	 * riferimento a DTO XmlDeliveryDate per DELIVERY_DATE
	 */
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private final XmlDeliveryDate deliveryDate;
	
	/**
	 * Riferimento a lista di DTO XmlParty per PARTY. Jackson crea un tag wrapper PARTIES attorno ai PARTY
	 */
    @JacksonXmlElementWrapper(localName = "PARTIES", useWrapping = true) 
    @JacksonXmlProperty(localName = "PARTY")  
	private final List<XmlParty> orderParties;
    
    /**
     * Riferimento a DTO XmlOrderPartiesReference per ORDER_PARTIES_REFERENCE
     */
    @JacksonXmlProperty(localName = "ORDER_PARTIES_REFERENCE")
    private final XmlOrderPartiesReference orderPartiesReference;

    /**
     * tag per valuta
     */
    @JacksonXmlProperty(localName= "bmecat:CURRENCY")
    private final String currency;
    
    
    /**
     * Costruttore per creare struttura XML-OpenTrans informazioni del header ordine partendo dal POJO {@code OrderHeader}
     * @param head - OrderHeader
     */
	public XmlOrderInfo(final OrderHeader head) {
		super();
		this.orderId = head.getOrderID();
		this.orderDate = head.getOrderDate();
		this.deliveryDate = new XmlDeliveryDate(head.getStartDate(), head.getEndDate(), DeliveryDateType.OPTIONAL);
		this.orderParties = new ArrayList<>();
		this.orderParties
				.addAll(
						Arrays.asList(
								new XmlParty(
										new XmlPartyID( head.getBuyerID(), PartyType.SUPPLIER_SPECIFIC)
										,"buyer"),
								new XmlParty(
										new XmlPartyID( head.getSupplierID(), PartyType.BUYER_SPECIFIC)
										,"supplier"),
								new XmlParty(
										new XmlPartyID( head.getDeliveryID(), PartyType.SUPPLIER_SPECIFIC)
										,"delivery")
								)
						);
		this.orderPartiesReference = new XmlOrderPartiesReference(
												head.getBuyerIDRef(), PartyType.SUPPLIER_SPECIFIC,
												head.getSupplierIDRef(), PartyType.BUYER_SPECIFIC,
												head.getDeliveryIDRef(), PartyType.SUPPLIER_SPECIFIC
											);
		this.currency = head.getCurrency();
	}

	
	/**
	 * 
	 * @return String
	 */
	public String getOrderId() {
		return orderId;
	}

	/**
	 * 
	 * @return String indicante una data
	 */
	public String getOrderDate() {
		return orderDate;
	}

	/**
	 * 
	 * @return XmlDeliveryDate indicante una data
	 */
	public XmlDeliveryDate getDeliveryDate() {
		return deliveryDate;
	}

	/**
	 * 
	 * @return List&lt;XmlParty&gt;
	 */
	public List<XmlParty> getOrderParties() {
		return orderParties;
	}

	/**
	 * 
	 * @return XmlOrderPartiesReference
	 */
	public XmlOrderPartiesReference getOrderPartiesReference() {
		return orderPartiesReference;
	}
	
	
}
