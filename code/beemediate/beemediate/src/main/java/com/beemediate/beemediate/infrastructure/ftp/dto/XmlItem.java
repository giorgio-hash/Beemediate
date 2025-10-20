package com.beemediate.beemediate.infrastructure.ftp.dto;

import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per articolo ordine. Può prendere in input il POJO {@code OrderItem}
 */
@JacksonXmlRootElement(localName = "ORDER_ITEM")
public class XmlItem {
	
	/**
	 * tag per ordinare l'articolo
	 */
	@JacksonXmlProperty(localName="LINE_ITEM_ID")
	private final int lineItemId;
	
	/**
	 * riferimento a DTO XmlProductId per PRODUCT_ID
	 */
	@JacksonXmlProperty(localName="PRODUCT_ID")
	private final XmlProductId prodId;
	
	/**
	 * tag per specificare quantità (con o senza cifre decimali; il separatore deve essere “.”)
	 */
	@JacksonXmlProperty(localName="QUANTITY")
	private final float quantity;
	
	/**
	 * tag per Unità di misura (unità ISO, ma è possibile una mappatura personalizzata)
	 */
	@JacksonXmlProperty(localName="bmecat:ORDER_UNIT")
	private final String orderUnit;

	
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans articolo ordine partendo dal POJO {@code OrderItem}
	 * @param item - OrderItem
	 */
	public XmlItem(final OrderItem item) {
		super();
		this.lineItemId = Integer.parseInt(item.getLineItemID());
		this.prodId = new XmlProductId(
								item.getSupplierID(),
								item.getBuyerID(),
								item.getDescriptionShort()
							);
		this.quantity = Float.parseFloat(item.getQuantity());
		this.orderUnit = item.getOrderUnit();
	}



	/**
	 * 
	 * @return int 
	 */
	public int getLineItemId() {
		return lineItemId;
	}



	/**
	 * 
	 * @return XmlProductId - DTO con numero articolo del sistema cliente e del sistema fornitore.
	 */
	public XmlProductId getProdId() {
		return prodId;
	}



	/**
	 * 
	 * @return float - quantità
	 */
	public float getQuantity() {
		return quantity;
	}



	/**
	 * 
	 * @return String - unità di misura (ISO) della quantità
	 */
	public String getOrderUnit() {
		return orderUnit;
	}


}