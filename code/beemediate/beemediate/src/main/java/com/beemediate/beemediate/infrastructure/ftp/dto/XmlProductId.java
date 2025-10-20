package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

/**
 * Mappatura XML-OpenTrans con identificativi del prodotto per ogni partner commerciale coinvolto nella transazione
 */
@JacksonXmlRootElement(localName = "PRODUCT_ID")
public class XmlProductId{	
	
	
	/**
	 * tag per Numero di articolo del fornitore
	 */
	@JacksonXmlProperty(localName="bmecat:SUPPLIER_PID")
	private final String supplierId;
	
	/**
	 * Riferimento a BuyerID per tag numero di articolo del cliente (opzionale)
	 */
	@JacksonXmlProperty(localName="bmecat:BUYER_PID")
	private final BuyerId buyerId;
	
	/**
	 * Tag contenente descrizione prodotto 
	 */
	@JacksonXmlProperty(localName="bmecat:DESCRIPTION_SHORT")
	private final String descriptionShort;
	
	/**
	 * Mappatura XML-OpenTrans con identificativi del prodotto dal sistema informativo del cliente
	 */
	public class BuyerId{
		
		/**
		 * identificativo prodotto nel sistema informativo del cliente
		 */
		@JacksonXmlText
		private final String buyerId;
		
		/**
		 * Attributo conforme al formato XML-OpenTrans desiderato
		 */
		@JacksonXmlProperty(isAttribute=true, localName="type")
		private static final String TYPE="CODE";
		
		/**
		 * Costruttore
		 * @param buyerId - String
		 */
		public BuyerId(String buyerId) {
			super();
			this.buyerId = buyerId;
		}
		
		/**
		 * 
		 * @return String
		 */
		public String getSupplierId() {
			return buyerId;
		}
		
		/**
		 * 
		 * @return String
		 */
		public String getType() {
			return TYPE;
		}
	}

	/**
	 * Costruttore
	 * @param supplierId - identificativo dell'articolo sul sistema fornitore
	 * @param buyerId - identificativo dell'articolo sul sistema cliente
	 * @param descriptionShort - descrizione dell'articolo
	 */
	public XmlProductId(final String supplierId, final String buyerId, final String descriptionShort) {
		super();
		this.supplierId = supplierId;
		this.buyerId = new BuyerId(buyerId);
		this.descriptionShort = descriptionShort;
	}

	/**
	 * 
	 * @return String
	 */
	public String getSupplierId() {
		return supplierId;
	}

	/**
	 * 
	 * @return BuyerID con identificativo ordine
	 */
	public BuyerId getBuyerId() {
		return buyerId;
	}

	/**
	 * 
	 * @return String
	 */
	public String getDescriptionShort() {
		return descriptionShort;
	}
	

}