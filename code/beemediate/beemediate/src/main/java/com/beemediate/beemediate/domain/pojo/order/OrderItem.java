package com.beemediate.beemediate.domain.pojo.order;

//import org.jmlspecs.annotation.SkipEsc;

/***Parte di OrderStructure. Contiene le informazioni relative ad un singolo articolo nell'ordine a fornitore. Ogni informazione è in formato String.*/
public class OrderItem {
	
	/***Numero di linea dell'articolo*/
	private /*@ spec_public @*/ String lineItemID = "";
	/***Numero con la quantità*/
	private /*@ spec_public @*/ String quantity = "";
	/***Unità di misura per la quantità*/
	private /*@ spec_public @*/ String orderUnit = "";
	
	//order_item.product_id
	/***identificativo del prodotto lato fornitore*/
	private /*@ spec_public @*/ String supplierID = "";
	/***identificativo del prodotto lato  cliente*/
	private /*@ spec_public @*/ String buyerID = "";
	/***descrizione aggiuntiva*/
	private /*@ spec_public @*/ String descriptionShort = "";
	
	/**
	 * Costruttore
	 */
	//@ public normal_behaviour
	/*@ ensures lineItemID!=null & quantity!=null & orderUnit!=null
	  @			& supplierID!=null & buyerID!=null & descriptionShort!=null;
	  @ pure
	  @*/
	public OrderItem() {/*empty constructor*/}
	
	/**
	 * 
	 * @return String - numero di linea dell'articolo
	 */
	//@ public normal_behaviour
	//@ ensures \result==lineItemID;
	public /*@ pure @*/ String getLineItemID() {
		return lineItemID;
	}
	
	/**
	 * 
	 * @param lineItemID - String
	 */
	//@ public normal_behaviour
	//@ ensures this.lineItemID!=null;
	public void setLineItemID(/*@ non_null @*/ final String lineItemID) {
		this.lineItemID = lineItemID;
	}
	
	/**
	 * 
	 * @return String - quantità
	 */
	//@ public normal_behaviour
	//@ ensures \result==quantity;
	public /*@ pure @*/ String getQuantity() {
		return quantity;
	}
	
	/**
	 * 
	 * @param quantity - String
	 */
	//@ public normal_behaviour
	//@ ensures this.quantity!=null;
	public void setQuantity(/*@ non_null @*/final String quantity) {
		this.quantity = quantity;
	}
	
	/**
	 * 
	 * @return String - l'unità di misura usata per specificare la quantità
	 */
	//@ public normal_behaviour
	//@ ensures \result==orderUnit;
	public /*@ pure @*/ String getOrderUnit() {
		return orderUnit;
	}
	
	/**
	 * 
	 * @param orderUnit - String
	 */
	//@ public normal_behaviour
	//@ ensures this.orderUnit!=null;
	public void setOrderUnit(/*@ non_null @*/ String orderUnit) {
		this.orderUnit = orderUnit;
	}
	
	/**
	 * 
	 * @return String - identificativo prodotto lato fornitore 
	 */
	//@ public normal_behaviour
	//@ ensures \result==supplierID;
	public /*@ pure @*/ String getSupplierID() {
		return supplierID;
	}
	
	/**
	 * 
	 * @return String - identificativo prodotto lato cliente
	 */
	//@ public normal_behaviour
	//@ ensures \result==buyerID;
	public String getBuyerID() {
		return buyerID;
	}
	
	/**
	 * 
	 * @return String - descrizione
	 */
	//@ public normal_behaviour
	//@ ensures \result==descriptionShort;
	public /*@ pure @*/ String getDescriptionShort() {
		return descriptionShort;
	}
	
	/**
	 * 
	 * @param supplierID - String 
	 */
	//@ public normal_behaviour
	//@ ensures this.supplierID!=null;
	public void setSupplierID(/*@ non_null @*/final String supplierID) {
		this.supplierID = supplierID;
	}
	
	/**
	 * 
	 * @param buyerID - String
	 */
	//@ public normal_behaviour
	//@ ensures this.buyerID!=null;
	public void setBuyerID(/*@ non_null @*/final String buyerID) {
		this.buyerID = buyerID;
	}
	
	/**
	 * 
	 * @param descriptionShort - String
	 */
	//@ public normal_behaviour
	//@ ensures this.descriptionShort!=null;
	public void setDescriptionShort(/*@ non_null @*/final String descriptionShort) {
		this.descriptionShort = descriptionShort;
	}
	
//	@SkipEsc
	@Override
	public String toString() {
		return "OrderItem [lineItemID=" + lineItemID + ", quantity=" + quantity + ", orderUnit=" + orderUnit
				+ ", supplierID=" + supplierID + ", buyerID=" + buyerID + ", descriptionShort=" + descriptionShort
				+ "]";
	}
	
	

}
