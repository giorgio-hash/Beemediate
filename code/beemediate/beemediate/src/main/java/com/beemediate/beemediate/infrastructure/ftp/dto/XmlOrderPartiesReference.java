package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "ORDER_PARTIES_REFERENCE")
public class XmlOrderPartiesReference {

	public class ShipmentPartiesReference{
		
		@JacksonXmlProperty(localName="DELIVERY_IDREF")
		private XmlPartyID deliveryIdRef;

		public ShipmentPartiesReference(XmlPartyID deliveryIdRef) {
			super();
			this.deliveryIdRef = deliveryIdRef;
		}

		public XmlPartyID getDeliveryIdRef() {
			return deliveryIdRef;
		}

		public void setDeliveryIdRef(XmlPartyID deliveryIdRef) {
			this.deliveryIdRef = deliveryIdRef;
		}
			
	}
	
	@JacksonXmlProperty(localName="BUYER_IDREF")
	private XmlPartyID buyerIdRef;
	@JacksonXmlProperty(localName="SUPPLIER_IDREF")
	private XmlPartyID supplierIdRef;
	@JacksonXmlProperty(localName="SHIPMENT_PARTIES_REFERENCE")
	private ShipmentPartiesReference shipmentPartiesRef;
	
	public XmlOrderPartiesReference(String buyerIdRef, String supplierIdRef,
			String shipmentPartiesRef) {
		super();
		this.buyerIdRef = new XmlPartyID( buyerIdRef, PartyType.SUPPLIER_SPECIFIC);
		this.supplierIdRef = new XmlPartyID( supplierIdRef, PartyType.BUYER_SPECIFIC);
		this.shipmentPartiesRef = new ShipmentPartiesReference(
											new XmlPartyID( shipmentPartiesRef, PartyType.SUPPLIER_SPECIFIC)
										);
	}

	public XmlPartyID getBuyerIdRef() {
		return buyerIdRef;
	}

	public XmlPartyID getSupplierIdRef() {
		return supplierIdRef;
	}

	public ShipmentPartiesReference getShipmentPartiesRef() {
		return shipmentPartiesRef;
	}
	
	
}
