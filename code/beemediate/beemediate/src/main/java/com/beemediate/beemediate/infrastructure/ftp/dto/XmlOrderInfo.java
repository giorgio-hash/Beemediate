package com.beemediate.beemediate.infrastructure.ftp.dto;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlElementWrapper;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER_INFO")
public class XmlOrderInfo {
	
	public class XmlDeliveryDate{
		
		@JacksonXmlProperty(isAttribute=true)
		private final String type = "optional";
		
		@JacksonXmlProperty(localName="DELIVERY_START_DATE")
		private String deliveryStartDate;
		
		@JacksonXmlProperty(localName="DELIVERY_END_DATE")
		private String deliveryEndDate;
		
		public XmlDeliveryDate(String deliveryStartDate, String deliveryEndDate) {
			super();
			this.deliveryStartDate = deliveryStartDate;
			this.deliveryEndDate = deliveryEndDate;
		}
		
		public String getDeliveryStartDate() {
			return deliveryStartDate;
		}
		
		public String getDeliveryEndDate() {
			return deliveryEndDate;
		}
		
	}
	
	@JacksonXmlProperty(localName="ORDER_ID")
	private String orderId;
	
	@JacksonXmlProperty(localName="ORDER_DATE")
	private String orderDate;
	
	@JacksonXmlProperty(localName="DELIVERY_DATE")
	private XmlDeliveryDate deliveryDate;
	
    @JacksonXmlElementWrapper(localName = "PARTIES", useWrapping = true) 
    @JacksonXmlProperty(localName = "PARTY")  
	private List<XmlParty> orderParties;
    
    @JacksonXmlProperty(localName = "ORDER_PARTIES_REFERENCE")
    private XmlOrderPartiesReference orderPartiesReference;

    @JacksonXmlProperty(localName= "bmecat:CURRENCY")
    private String currency;
    
    
	public XmlOrderInfo(OrderHeader head) {
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

	
	
	public String getOrderId() {
		return orderId;
	}

	public String getOrderDate() {
		return orderDate;
	}

	public XmlDeliveryDate getDeliveryDate() {
		return deliveryDate;
	}

	public List<XmlParty> getOrderParties() {
		return orderParties;
	}

	public XmlOrderPartiesReference getOrderPartiesReference() {
		return orderPartiesReference;
	}

    
}
