package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlText;

@JacksonXmlRootElement(localName = "PRODUCT_ID")
public class XmlProductId{	
	
	public class BuyerId{
		
		@JacksonXmlText
		private String buyerId;
		
		@JacksonXmlProperty(isAttribute=true)
		private final String type="CODE";
		
		public BuyerId(String buyerId) {
			super();
			this.buyerId = buyerId;
		}
		
		public String getSupplierId() {
			return buyerId;
		}
		
		public String getType() {
			return type;
		}
	}
	
	@JacksonXmlProperty(localName="bmecat:SUPPLIER_PID")
	private String supplierId;
	
	@JacksonXmlProperty(localName="bmecat:BUYER_PID")
	private BuyerId buyerId;
	
	@JacksonXmlProperty(localName="bmecat:DESCRIPTION_SHORT")
	private String descriptionShort;

	public XmlProductId(String supplierId, String buyerId, String descriptionShort) {
		super();
		this.supplierId = supplierId;
		this.buyerId = new BuyerId(buyerId);
		this.descriptionShort = descriptionShort;
	}

	public String getSupplierId() {
		return supplierId;
	}

	public BuyerId getBuyerId() {
		return buyerId;
	}

	public String getDescriptionShort() {
		return descriptionShort;
	}
	

}