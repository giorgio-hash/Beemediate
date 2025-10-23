package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.PartyType;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlShipmentPartiesReference;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlPartyID;
import com.fasterxml.jackson.annotation.JsonInclude;
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
	private XmlPartyID buyerIdRef;
	/**
	 * RIferimento a XmlPartyID con Informazioni sul fornitore
	 */
	@JacksonXmlProperty(localName="SUPPLIER_IDREF")
	private XmlPartyID supplierIdRef;
	/**
	 * Riferimento a ShipmentPartiesReference con informazioni sul luogo di consegna
	 */
	@JacksonXmlProperty(localName="SHIPMENT_PARTIES_REFERENCE")
	@JsonInclude(JsonInclude.Include.NON_NULL)
	private XmlShipmentPartiesReference shipmentPartiesRef;
	
	
	/**
	 * Empty Constructor for Jackson deserializer
	 */
	public XmlOrderPartiesReference() {/*Empty Constructor for Jackson deserializer*/}
	
	/**
	 * Costruttore 
	 * @param buyerIdRef - String con informazioni sul cliente
	 * @param buyerIdType - ulteriori informazioni sul buyerIdRef
	 * @param supplierIdRef - String con informazioni sul fornitore
	 * @param supplierIdType - ulteriori informazioni sul supplierIdRef
	 * @param shipmentPartiesRef - String con informazioni sul luogo di destinazione
	 * @param shipmentPartyType - ulteriori informazioni sul tipo di spedizione
	 */
	public XmlOrderPartiesReference(String buyerIdRef, PartyType buyerIdType, String supplierIdRef, PartyType supplierIdType,
			String shipmentPartiesRef, PartyType shipmentPartyType) {
		super();
		this.buyerIdRef = new XmlPartyID( buyerIdRef, buyerIdType);
		this.supplierIdRef = new XmlPartyID( supplierIdRef, supplierIdType);
		this.shipmentPartiesRef = new XmlShipmentPartiesReference(
											new XmlPartyID( shipmentPartiesRef, shipmentPartyType)
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
	public XmlShipmentPartiesReference getShipmentPartiesRef() {
		return shipmentPartiesRef;
	}

	/**
	 * 
	 * @param buyerIdRef - XmlPartyID
	 */
	public void setBuyerIdRef(XmlPartyID buyerIdRef) {
		this.buyerIdRef = buyerIdRef;
	}

	/**
	 * 
	 * @param supplierIdRef - XmlPartyID
	 */
	public void setSupplierIdRef(XmlPartyID supplierIdRef) {
		this.supplierIdRef = supplierIdRef;
	}

	/**
	 * 
	 * @param buyerIdRef - ShipmentPartiesReference
	 */
	public void setShipmentPartiesRef(XmlShipmentPartiesReference shipmentPartiesRef) {
		this.shipmentPartiesRef = shipmentPartiesRef;
	}
	
	
	
}
