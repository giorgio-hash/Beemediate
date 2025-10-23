package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.PartyType;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlPartyID;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans con dati di riferimento sintetici dei partner commerciali
 */
@JacksonXmlRootElement(localName = "ORDER_PARTIES_REFERENCE")
public class XmlOrderPartiesReference {

	/**
	 * Riferimentoa XmlPartyID con Informazioni sul cliente
	 */
	@JacksonXmlProperty(localName="BUYER_IDREF")
	private final XmlPartyID buyerIdRef;
	/**
	 * RIferimento a XmlPartyID con Informazioni sul fornitore
	 */
	@JacksonXmlProperty(localName="SUPPLIER_IDREF")
	private final XmlPartyID supplierIdRef;
	/**
	 * Riferimento a ShipmentPartiesReference con informazioni sul luogo di consegna
	 */
	@JacksonXmlProperty(localName="SHIPMENT_PARTIES_REFERENCE")
	private final ShipmentPartiesReference shipmentPartiesRef;
	
	/**
	 * Mappatura XML-OpenTrans con informazioni di destinazione
	 */
	public class ShipmentPartiesReference{
		
		/**
		 * Riferimento ad XmlPartyID per DELIVERY_IDREF, con identificativo del luogo di destinazione
		 */
		@JacksonXmlProperty(localName="DELIVERY_IDREF")
		private final XmlPartyID deliveryIdRef;

		/**
		 * Costruttore con identificativo del luogo di destinazione
		 * @param deliveryIdRef
		 */
		public ShipmentPartiesReference(final XmlPartyID deliveryIdRef) {
			super();
			this.deliveryIdRef = deliveryIdRef;
		}

		/**
		 * 
		 * @return XmlPartyID con identificativo di destinazione
		 */
		public final XmlPartyID getDeliveryIdRef() {
			return deliveryIdRef;
		}
			
	}
	
	
	/**
	 * Costruttore 
	 * @param buyerIdRef - String con informazioni sul cliente
	 * @param supplierIdRef - String con informazioni sul fornitore
	 * @param shipmentPartiesRef - String con informazioni sul luogo di destinazione
	 */
	public XmlOrderPartiesReference(final String buyerIdRef, final String supplierIdRef, final String shipmentPartiesRef) {
		super();
		this.buyerIdRef = new XmlPartyID( buyerIdRef, PartyType.SUPPLIER_SPECIFIC);
		this.supplierIdRef = new XmlPartyID( supplierIdRef, PartyType.BUYER_SPECIFIC);
		this.shipmentPartiesRef = new ShipmentPartiesReference(
											new XmlPartyID( shipmentPartiesRef, PartyType.SUPPLIER_SPECIFIC)
										);
	}

	/**
	 * 
	 * @return XmlPartyID con informazioni sul cliente
	 */
	public XmlPartyID getBuyerIdRef() {
		return buyerIdRef;
	}

	/**
	 * 
	 * @return XmlPartyID con informazioni sul fornitore
	 */
	public XmlPartyID getSupplierIdRef() {
		return supplierIdRef;
	}

	/**
	 * 
	 * @return XmlPartyID con informazioni sul luogo di destinazione
	 */
	public ShipmentPartiesReference getShipmentPartiesRef() {
		return shipmentPartiesRef;
	}
	
	
}
