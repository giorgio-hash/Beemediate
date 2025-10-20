package com.beemediate.beemediate.infrastructure.ftp.dto;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
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
	 * Mappatura XML-OpenTrans per struttura informazioni relative alle date per la consegna desiderati dal cliente.
	 */
	public class XmlDeliveryDate{
		
		/**
		 * Attributo obbligatorio per conformità col formato XML-OpenTrans del fornitore
		 */
		@JacksonXmlProperty(isAttribute=true, localName="type")
		private static final String TYPE = "optional";
		
		/*
		 * Data inizio periodo di consegna desiderata dal cliente (N.B. è richiesto sia uguale a DELIVERY_END_DATE)
		 */
		@JacksonXmlProperty(localName="DELIVERY_START_DATE")
		private final String deliveryStartDate;
		
		/*
		 * Data fine periodo di consegna desiderata dal cliente (N.B. è richiesto sia uguale a DELIVERY_START_DATE)
		 */
		@JacksonXmlProperty(localName="DELIVERY_END_DATE")
		private final String deliveryEndDate;
		
		/**
		 * Costruttore per creare struttura XML-OpenTrans data di consegna
		 * @param deliveryStartDate - String con data in formato opportuno
		 * @param deliveryEndDate - String con data in formato opportuno
		 */
		public XmlDeliveryDate(final String deliveryStartDate, final String deliveryEndDate) {
			super();
			this.deliveryStartDate = deliveryStartDate;
			this.deliveryEndDate = deliveryEndDate;
		}
		
		/**
		 * 
		 * @return String specificante data
		 */
		public String getDeliveryStartDate() {
			return deliveryStartDate;
		}
		
		/**
		 * 
		 * @return String specificante data
		 */
		public String getDeliveryEndDate() {
			return deliveryEndDate;
		}
		
	}
    
    
    /**
     * Costruttore per creare struttura XML-OpenTrans informazioni del header ordine partendo dal POJO {@code OrderHeader}
     * @param head - OrderHeader
     */
	public XmlOrderInfo(final OrderHeader head) {
		super();
		this.orderId = head.getOrderID();
		this.orderDate = head.getOrderDate();
		this.deliveryDate = new XmlDeliveryDate(head.getStartDate(), head.getEndDate());
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
											head.getBuyerIDRef(),
											head.getSupplierIDRef(),
											head.getDeliveryIDRef()
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
	 * @return String indicante una data
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
