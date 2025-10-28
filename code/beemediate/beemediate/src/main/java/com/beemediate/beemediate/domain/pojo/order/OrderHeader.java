package com.beemediate.beemediate.domain.pojo.order;

//import org.jmlspecs.annotation.SkipEsc;

/**
 * Parte di OrderStructure. Contiene le informazioni principali dell'ordine. Tutte le informazioni sono in formato String.
 */
public class OrderHeader {
	
	//order_info
	/***Identificativo dell'ordine*/
	private /*@ spec_public @*/ String orderID = "";
	/***Data di creazione ordine*/
	private /*@ spec_public @*/ String orderDate = "";
	/***Valuta*/
	private /*@ spec_public @*/ String currency = "";
	
	//order_info.parties.party[party_role="buyer"]
	/***Identificativo del cliente sul sistema fornitore*/
	private /*@ spec_public @*/ String buyerID = "";
	//order_info.parties.party[party_role="supplier"]
	/***Identificativo del fornitore*/
	private /*@ spec_public @*/ String supplierID = "";
	//order_info.parties.party[party_role="delivery"]
	/***Identificativo del luogo di consegna*/
	private /*@ spec_public @*/ String deliveryID = "";
	
	//order_info.delivery_date
	/***data di evacuazione ordine*/
	private /*@ spec_public @*/ String startDate = "";
	/***data di consegna*/
	private /*@ spec_public @*/ String endDate = "";
	
	//order_info.order_parties_reference
	/***Identificativo di riferimento al cliente*/
	private /*@ spec_public @*/ String buyerIDRef = "";
	/***Identificativo di riferimento al fornitore*/
	private /*@ spec_public @*/ String supplierIDRef = "";
	
	//order_info.parties_reference.shipment_parties_reference
	/***Identificativo di riferimento alla consegna*/
	private /*@ spec_public @*/ String deliveryIDRef = "";
	
	/**
	 * Costruttore
	 */
	/*@ ensures buyerID!=null & supplierID!=null & deliveryID!=null
	  @			& startDate!=null & endDate!=null
	  @			& buyerIDRef!=null & supplierIDRef!=null
	  @			& deliveryIDRef!=null;
	  @*/
	//@ pure
	public OrderHeader() {/*empty constructor*/}
	
	/**
	 * Copy Constructor
	 */
	/*@
	  @ public normal_behaviour
	  @ requires copy!=null;
	  @ ensures this.buyerID == copy.buyerID &
		this.buyerIDRef == copy.buyerIDRef &
		this.currency == copy.currency &
		this.deliveryID == copy.deliveryID &
		this.deliveryIDRef == copy.deliveryIDRef &
		this.endDate == copy.endDate &
		this.orderDate == copy.orderDate &
		this.orderID == copy.orderID &
		this.startDate == copy.startDate &
		this.supplierID == copy.supplierID &
		this.supplierIDRef == copy.supplierIDRef;
	  @ ensures this != copy;
	  @ ensures \not_modified(copy);
	  @*/
	public OrderHeader(OrderHeader copy) {
		this.buyerID = copy.buyerID;
		this.buyerIDRef = copy.buyerIDRef ;
		this.currency = copy.currency;
		this.deliveryID = copy.deliveryID;
		this.deliveryIDRef = copy.deliveryIDRef;
		this.endDate = copy.endDate;
		this.orderDate = copy.orderDate;
		this.orderID = copy.orderID;
		this.startDate = copy.startDate;
		this.supplierID = copy.supplierID;
		this.supplierIDRef = copy.supplierIDRef;
	}
	
	/**
	 * 
	 * @return String - identificativo ordine
	 */
	//@ public normal_behaviour
	//@ ensures \result == orderID;
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

	/**
	 * Imposta identificativo ordine
	 * @param orderID - oggetto String
	 */
	//@ public normal_behaviour
	//@ ensures this.orderID!=null;
	public void setOrderID( /*@ non_null @*/final String orderID) {
		this.orderID = orderID;
	}

	/**
	 * 
	 * @return String - data creazione ordine
	 */
	//@ public normal_behaviour
	//@ ensures \result==orderDate;
	public /*@ pure @*/  String getOrderDate() {
		return orderDate;
	}

	/**
	 * Imposta data creazione ordine
	 * @param orderDate - data ordine
	 */
	//@ public normal_behaviour
	//@ ensures this.orderDate!=null;
	public void setOrderDate( /*@ non_null @*/final String orderDate) {
		this.orderDate = orderDate;
	}

	/**
	 * 
	 * @return String - Valuta
	 */
	//@ public normal_behaviour
	//@ ensures \result==currency;
	public /*@ pure @*/  String getCurrency() {
		return currency;
	}

	/**
	 * Imposta la valuta
	 * @param currency - String valuta
	 */
	//@ public normal_behaviour
	//@ ensures this.currency!=null;
	public void setCurrency( /*@ non_null @*/final String currency) {
		this.currency = currency;
	}

	/**
	 * 
	 * @return String - identificativo cliente (sul sistema fornitore)
	 */
	//@ public normal_behaviour
	//@ ensures \result==buyerID;
	public /*@ pure @*/  String getBuyerID() {
		return buyerID;
	}

	/**
	 * 
	 * @param buyerID - identificativo String cliente (sul sistema fornitore)
	 */
	//@ public normal_behaviour
	//@ ensures this.buyerID!=null;
	public void setBuyerID( /*@ non_null @*/final String buyerID) {
		this.buyerID = buyerID;
	}

	/**
	 * 
	 * @return String - identificativo cliente
	 */
	//@ public normal_behaviour
	//@ ensures \result==supplierID;
	public /*@ pure @*/ String getSupplierID() {
		return supplierID;
	}

	/**
	 * 
	 * @param supplierID - identificativo String fornitore
	 */
	//@ public normal_behaviour
	//@ ensures this.supplierID!=null;
	public void setSupplierID( /*@ non_null @*/final String supplierID) {
		this.supplierID = supplierID;
	}

	/**
	 * 
	 * @return String - identificativo del luogo di consegna
	 */
	//@ public normal_behaviour
	//@ ensures \result==deliveryID;
	public /*@ pure @*/ String getDeliveryID() {
		return deliveryID;
	}

	/**
	 * 
	 * @param deliveryID - identificativo String del luogo di consegna
	 */
	//@ public normal_behaviour
	//@ ensures this.deliveryID==deliveryID;
	public void setDeliveryID( /*@ non_null @*/final String deliveryID) {
		this.deliveryID = deliveryID;
	}

	/**
	 * 
	 * @return String - data di inizio spedizione
	 */
	//@ public normal_behaviour
	//@ ensures \result==startDate;
	public /*@ pure @*/ String getStartDate() {
		return startDate;
	}

	/**
	 * 
	 * @param startDate - data String di inizio spedizione
	 */
	//@ public normal_behaviour
	//@ ensures this.startDate!=null;
	public void setStartDate( /*@ non_null @*/final String startDate) {
		this.startDate = startDate;
	}

	/**
	 * 
	 * @return String - data di consegna
	 */
	//@ public normal_behaviour
	//@ ensures \result == endDate;
	public /*@ pure @*/ String getEndDate() {
		return endDate;
	}

	/**
	 * 
	 * @param endDate - data String di consegna
	 */
	//@ public normal_behaviour
	//@ ensures this.endDate!=null;
	public void setEndDate(/*@ non_null @*/final String endDate) {
		this.endDate = endDate;
	}

	/**
	 * 
	 * @return String - riferimento identificativo cliente sul sistema fornitore
	 */
	//@ public normal_behaviour
	//@ ensures \result==buyerIDRef;
	public /*@ pure @*/ String getBuyerIDRef() {
		return buyerIDRef;
	}

	/**
	 * 
	 * @param buyerIDRef - String
	 */
	//@ public normal_behaviour
	//@ ensures this.buyerIDRef!=null; 
	public void setBuyerIDRef(/*@ non_null @*/final String buyerIDRef) {
		this.buyerIDRef = buyerIDRef;
	}

	/**
	 * 
	 * @return String - riferimento all'identificativo fornitore
	 */
	//@ public normal_behaviour
	//@ ensures \result==supplierIDRef;
	public /*@ pure @*/ String getSupplierIDRef() {
		return supplierIDRef;
	}

	/**
	 * 
	 * @param supplierIDRef - riferimento String all'identificativo fornitore
	 */
	//@ public normal_behaviour
	//@ ensures this.supplierIDRef!=null;
	public void setSupplierIDRef(/*@ non_null @*/final String supplierIDRef) {
		this.supplierIDRef = supplierIDRef;
	}

	/**
	 * 
	 * @return String - riferimento all'identificativo del luogo di consegna
	 */
	//@ public normal_behaviour
	//@ ensures \result==deliveryIDRef;
	public /*@ pure @*/ String getDeliveryIDRef() {
		return deliveryIDRef;
	}

	/**
	 * 
	 * @param deliveryIDRef - String
	 */
	//@ public normal_behaviour
	//@ ensures this.deliveryIDRef!=null;
	public void setDeliveryIDRef(/*@ non_null @*/final String deliveryIDRef) {
		this.deliveryIDRef = deliveryIDRef;
	}

//	@SkipEsc
	@Override
	public String toString() {
		return "OrderHeader [orderID=" + orderID + ", orderDate=" + orderDate + ", currency=" + currency + ", buyerID="
				+ buyerID + ", supplierID=" + supplierID + ", deliveryID=" + deliveryID + ", startDate=" + startDate
				+ ", endDate=" + endDate + ", buyerIDRef=" + buyerIDRef + ", supplierIDRef=" + supplierIDRef
				+ ", deliveryIDRef=" + deliveryIDRef + "]";
	}

	
	
}
