package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlProductID;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per articolo ordine. Può prendere in input il POJO {@code OrderItem}
 */
@JacksonXmlRootElement(localName = "ORDER_ITEM")
public final class XmlItem {
	
	/**
	 * tag per ordinare l'articolo
	 */
	@JacksonXmlProperty(localName="LINE_ITEM_ID")
	private int lineItemId;
	
	/**
	 * riferimento a DTO XmlProductId per PRODUCT_ID
	 */
	@JacksonXmlProperty(localName="PRODUCT_ID")
	private XmlProductID prodId;
	
	/**
	 * tag per specificare quantità (con o senza cifre decimali; il separatore deve essere “.”)
	 */
	@JacksonXmlProperty(localName="QUANTITY")
	private float quantity;
	
	/**
	 * tag per Unità di misura (unità ISO, ma è possibile una mappatura personalizzata)
	 */
	@JacksonXmlProperty(localName="bmecat:ORDER_UNIT")
	private String orderUnit;

	
	/**
	 * empty constructor for deserializer
	 */
	public XmlItem() {/*empty constructor*/}
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans articolo ordine partendo dal POJO {@code OrderItem}
	 * @param item - OrderItem
	 */
	public XmlItem(final OrderItem item) {
		super();
		this.lineItemId = Integer.parseInt(item.getLineItemID());
		this.prodId = new XmlProductID(
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
	public XmlProductID getProdId() {
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



	public void setLineItemId(int lineItemId) {
		this.lineItemId = lineItemId;
	}



	public void setProdId(XmlProductID prodId) {
		this.prodId = prodId;
	}



	public void setQuantity(float quantity) {
		this.quantity = quantity;
	}



	public void setOrderUnit(String orderUnit) {
		this.orderUnit = orderUnit;
	}

	

}