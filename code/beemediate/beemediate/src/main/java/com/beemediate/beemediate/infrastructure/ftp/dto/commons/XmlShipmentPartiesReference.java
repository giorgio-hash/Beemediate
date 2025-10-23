package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans con informazioni di destinazione
 */
@JacksonXmlRootElement(localName="SHIPMENT_PARTIES_REFERENCE")
public class XmlShipmentPartiesReference{
	
	@JacksonXmlProperty(localName="DELIVERY_IDREF")
	private XmlPartyID deliveryIdRef;

	/**
	 * Empty Constructor for Jackson deserializer
	 */
	public XmlShipmentPartiesReference() {/*Empty Constructor for Jackson deserializer*/}
	
	/**
	 * Costruttore con identificativo del luogo di destinazione
	 * @param deliveryIdRef
	 */
	public XmlShipmentPartiesReference(XmlPartyID deliveryIdRef) {
		super();
		this.deliveryIdRef = deliveryIdRef;
	}

	/**
	 * 
	 * @return XmlPartyID con identificativo di destinazione
	 */
	public XmlPartyID getDeliveryIdRef() {
		return deliveryIdRef;
	}

	/**
	 * 
	 * @param deliveryIdRef
	 */
	public void setDeliveryIdRef(XmlPartyID deliveryIdRef) {
		this.deliveryIdRef = deliveryIdRef;
	}
}