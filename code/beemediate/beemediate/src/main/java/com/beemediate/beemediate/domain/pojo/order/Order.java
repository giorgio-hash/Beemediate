package com.beemediate.beemediate.domain.pojo.order;

/***Classe per gestire l'ordine*/
public class Order {
	
	/***struttura dati dell'ordine*/
	private /*@ spec_public @*/ final OrderStructure data;
	
	/***identificativo dell' ordine*/
	private /*@ spec_public @*/ final String orderID;
	
	//campi pi� importanti per controllo errori
	/***Controllo errori nei campi che fanno riferimento al numero cliente*/
	private /*@ spec_public @*/ boolean customerNumber;
	/***Controllo errori nei campi che fanno riferimento al numero articolo*/
	private /*@ spec_public @*/ boolean articleNumber;
	/***Controllo errori nei campi che fanno riferimento all'unità di misura per la quantità articolo*/
	private /*@ spec_public @*/ boolean quantityMeasure;
	/***Controllo errori nei campi che fanno riferimento alla quantità articolo*/
	private /*@ spec_public @*/ QuantityFieldValue quantity;
	/***Controllo errori nei campi che fanno riferimento all'identificativo del luogo di consegna*/
	private /*@ spec_public @*/ boolean deliveryLocationNumber;
	/***Controllo errori nei campi che fanno riferimento alla data di consegna*/
	private /*@ spec_public @*/ boolean deliveryDate;
	/***Controllo errori nei campi che fanno riferimento al contenut della data di consegna*/
	private /*@ spec_public @*/ boolean deliveryDateContent;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant quantity != null; @*/
	/*@ public invariant orderID != null; @*/
	
	/**
	 * Costruttore
	 * @param d - oggetto OrderStructure per struttura dati ordine
	 * @param oID - identificativo String dell'ordine
	 */
	/*@ public normal_behaviour
	  @ requires d != null & oID!=null;
	  @ ensures data == d && orderID == oID 
	  @						&& quantity == QuantityFieldValue.NAN
	  @						&& !customerNumber && !articleNumber && !quantityMeasure 
	  @						&& !deliveryLocationNumber && !deliveryDate && !deliveryDateContent;						
	  @ pure
	  @*/
	public Order(/*@ non_null*/final OrderStructure d,final String oID) {
		data = d;
		orderID = oID;
		quantity = QuantityFieldValue.NAN;
		customerNumber = articleNumber = quantityMeasure = deliveryLocationNumber = deliveryDate = deliveryDateContent = false;
	}

	/**
	 * Restituisce una copia difensiva (CWE-374) della struttura dati dell'ordine.
	 * @return oggetto OrderStructure
	 */
	/*@ public normal_behaviour
	  @ requires data!=null & data.header!=null & data.itemList!=null & data.orderSummary!=null;
	  @ requires data.itemList.length>0 
	  				& (\forall int i; 0 <= i & i < data.itemList.length; data.itemList[i] != null)
	  				& (\forall int i; 0<=i & i<data.itemList.length; \typeof(data.itemList[i]) == \type(OrderItem) )
	  				& \elemtype(\typeof(data.itemList)) == \type(OrderItem)
	  				& data.orderSummary.totalItemNum == data.itemList.length; 
	  @ ensures \result != null;
	  @ ensures \result != data; 
	  @*/
	public /*@ pure @*/ OrderStructure getData() {
		return new OrderStructure(data);
	}

	/**
	 *  
	 * @return <tt>true</tt> se la combinazione di errori identifica un errore XMLOpenTrans non bloccante di tipo "ContentError"
	 */
	//@ public normal_behaviour
	//@ ensures \result == (!articleNumber | !quantityMeasure | (deliveryDate & !deliveryDateContent) );
	public /*@ pure @*/ boolean hasContentError() {
		return !(articleNumber && quantityMeasure && (!deliveryDate || deliveryDateContent));
	}

	/**
	 * 
	 * @return <tt>true</tt> se la combinazione di errori identifica un errore XMLOpenTrans bloccante di tipo "OpenTransError"
	 */
	//@ public normal_behaviour
	//@ requires quantity != null;
	//@ ensures \result == (!customerNumber | !deliveryLocationNumber | !deliveryDate | quantity != QuantityFieldValue.FLOAT_WITH_DOT);
	public /*@ pure @*/ boolean hasOpenTransError() {
		return !(customerNumber && deliveryLocationNumber && deliveryDate && quantity == QuantityFieldValue.FLOAT_WITH_DOT);
	}

	/**
	 * 
	 * @return <tt>true</tt> se il numero cliente risulta errato
	 */
	//@ public normal_behaviour
	//@ ensures \result == customerNumber;
	public /*@ pure @*/ boolean isCustomerNumber() {
		return customerNumber;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori nel numero cliente
	 * @param cn - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable customerNumber;
	//@ ensures customerNumber == cn;
	public void setCustomerNumber(final boolean cn) {
		customerNumber = cn;
	}

	/**
	 * 
	 * @return <tt>true</tt> se esiste numero articolo errato
	 */
	//@ public normal_behaviour
	//@ ensures \result == articleNumber;
	public /*@ pure @*/ boolean isArticleNumber() {
		return articleNumber;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori nel numero articolo
	 * @param an - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable articleNumber;
	//@ ensures articleNumber == an;
	public void setArticleNumber(final boolean an) {
		articleNumber = an;
	}

	/**
	 * 
	 * @return <tt>true</tt> se esiste unità di misura della quantità errato
	 */
	//@ public normal_behaviour
	//@ ensures \result == quantityMeasure;
	public /*@ pure @*/ boolean isQuantityMeasure() {
		return quantityMeasure;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori  nell'unità di misura per la quantità articolo
	 * @param qm - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable quantityMeasure;
	//@ensures quantityMeasure == qm;
	public void setQuantityMeasure(final boolean qm) {
		quantityMeasure = qm;
	}

	/**
	 * 
	 * @return valore enum QuantityFieldValue
	 */
	//@ public normal_behaviour
	//@ ensures \result == quantity;
	public /*@ pure @*/ QuantityFieldValue getQuantity() {
		return quantity;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori  nella quantità articolo
	 * @param q - valore QuantityFieldValue
	 */
	//@ public normal_behaviour
	//@ assignable quantity;
	//@ requires q != null;
	//@ ensures quantity == q;
	public void setQuantity(final QuantityFieldValue q) {
		quantity = q;
	}

	/**
	 * 
	 * @return <tt>true</tt> se il numero del luogo di consegna risulta errato
	 */
	//@ public normal_behaviour
	//@ ensures \result == deliveryLocationNumber;
	public /*@ pure @*/ boolean isDeliveryLocationNumber() {
		return deliveryLocationNumber;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori  nell'identificativo del luogo di consegna
	 * @param dln - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable deliveryLocationNumber;
	//@ ensures deliveryLocationNumber == dln;
	public void setDeliveryLocationNumber(final boolean dln) {
		deliveryLocationNumber = dln;
	}

	/**
	 * 
	 * @return <tt>true</tt> se la data di consegna risulta errata
	 */
	//@ public normal_behaviour
	//@ ensures \result == deliveryDate;
	public /*@ pure @*/ boolean isDeliveryDate() {
		return deliveryDate;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori  nella data di consegna
	 * @param dd - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable deliveryDate;
	//@ ensures deliveryDate == dd;
	public void setDeliveryDate(final boolean dd) {
		deliveryDate = dd;
	}

	/**
	 * 
	 * @return <tt>true</tt> se il contenuto della data di consegna risulta errata
	 */
	//@ public normal_behaviour
	//@ ensures \result == deliveryDateContent;
	public /*@ pure @*/ boolean isDeliveryDateContent() {
		return deliveryDateContent;
	}

	/**
	 * Imposta la flag riguardo la presenza di errori nel contenuto della data di consegna
	 * @param ddc - imposta a <tt>true</tt> se c'è errore
	 */
	//@ public normal_behaviour
	//@ assignable deliveryDateContent;
	//@ ensures deliveryDateContent == ddc;
	public void setDeliveryDateContent(final boolean ddc) {
		deliveryDateContent = ddc;
	}
	
	/**
	 * 
	 * @return identificativo dell'ordine
	 */
	//@ public normal_behaviour
	//@ ensures \result == orderID; 
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

}
