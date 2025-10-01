package com.beemediate.beemediate.domain.pojo.order;

public class Order {
	
	//struttura dati
	private /*@ spec_public @*/ OrderStructure data;
	
	//identificativo
	private /*@ spec_public @*/ final String orderID;
	
	//campi pi� importanti per controllo errori
	private /*@ spec_public @*/ boolean customerNumber;
	private /*@ spec_public @*/ boolean articleNumber;
	private /*@ spec_public @*/ boolean quantityMeasure;
	private /*@ spec_public @*/ QuantityFieldValue quantity;
	private /*@ spec_public @*/ boolean deliveryLocationNumber;
	private /*@ spec_public @*/ boolean deliveryDate;
	private /*@ spec_public @*/ boolean deliveryDateContent;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant quantity != null; @*/
	/*@ public invariant orderID != null; @*/
	
	/*@ public normal_behaviour
	  @ requires d != null & oID!=null;
	  @ ensures data == d && orderID == oID 
	  @						&& quantity == QuantityFieldValue.NAN
	  @						&& !customerNumber && !articleNumber && !quantityMeasure 
	  @						&& !deliveryLocationNumber && !deliveryDate && !deliveryDateContent;						
	  @ pure
	  @*/
	public Order(/*@ non_null*/OrderStructure d, String oID) {
		data = d;
		orderID = oID;
		quantity = QuantityFieldValue.NAN;
		customerNumber = articleNumber = quantityMeasure = deliveryLocationNumber = deliveryDate = deliveryDateContent = false;
	}

	//@ public normal_behaviour
	//@ ensures \result == data;
	public /*@ pure @*/ OrderStructure getData() {
		return data;
	}

	//@ public normal_behaviour
	//@ ensures \result == (!articleNumber | !quantityMeasure | (deliveryDate & !deliveryDateContent) );
	public /*@ pure @*/ boolean hasContentError() {
		return !(articleNumber && quantityMeasure && (!deliveryDate || deliveryDateContent));
	}

	//@ public normal_behaviour
	//@ requires quantity != null;
	//@ ensures \result == (!customerNumber | !deliveryLocationNumber | !deliveryDate | quantity != QuantityFieldValue.FLOAT_WITH_DOT);
	public /*@ pure @*/ boolean hasOpenTransError() {
		return !(customerNumber && deliveryLocationNumber && deliveryDate && quantity == QuantityFieldValue.FLOAT_WITH_DOT);
	}

	//@ public normal_behaviour
	//@ ensures \result == customerNumber;
	public /*@ pure @*/ boolean isCustomerNumber() {
		return customerNumber;
	}

	//@ public normal_behaviour
	//@ assignable customerNumber;
	//@ ensures customerNumber == cn;
	public void setCustomerNumber(boolean cn) {
		customerNumber = cn;
	}

	//@ public normal_behaviour
	//@ ensures \result == articleNumber;
	public /*@ pure @*/ boolean isArticleNumber() {
		return articleNumber;
	}

	//@ public normal_behaviour
	//@ assignable articleNumber;
	//@ ensures articleNumber == an;
	public void setArticleNumber(boolean an) {
		articleNumber = an;
	}

	//@ public normal_behaviour
	//@ ensures \result == quantityMeasure;
	public /*@ pure @*/ boolean isQuantityMeasure() {
		return quantityMeasure;
	}

	//@ public normal_behaviour
	//@ assignable quantityMeasure;
	//@ensures quantityMeasure == qm;
	public void setQuantityMeasure(boolean qm) {
		quantityMeasure = qm;
	}

	//@ public normal_behaviour
	//@ ensures \result == quantity;
	public /*@ pure @*/ QuantityFieldValue getQuantity() {
		return quantity;
	}

	//@ public normal_behaviour
	//@ assignable quantity;
	//@ requires q != null;
	//@ ensures quantity == q;
	public void setQuantity(QuantityFieldValue q) {
		quantity = q;
	}

	//@ public normal_behaviour
	//@ ensures \result == deliveryLocationNumber;
	public /*@ pure @*/ boolean isDeliveryLocationNumber() {
		return deliveryLocationNumber;
	}

	//@ public normal_behaviour
	//@ assignable deliveryLocationNumber;
	//@ ensures deliveryLocationNumber == dln;
	public void setDeliveryLocationNumber(boolean dln) {
		deliveryLocationNumber = dln;
	}

	//@ public normal_behaviour
	//@ ensures \result == deliveryDate;
	public /*@ pure @*/ boolean isDeliveryDate() {
		return deliveryDate;
	}

	//@ public normal_behaviour
	//@ assignable deliveryDate;
	//@ ensures deliveryDate == dd;
	public void setDeliveryDate(boolean dd) {
		deliveryDate = dd;
	}

	//@ public normal_behaviour
	//@ ensures \result == deliveryDateContent;
	public /*@ pure @*/ boolean isDeliveryDateContent() {
		return deliveryDateContent;
	}

	//@ public normal_behaviour
	//@ assignable deliveryDateContent;
	//@ ensures deliveryDateContent == ddc;
	public void setDeliveryDateContent(boolean ddc) {
		deliveryDateContent = ddc;
	}
	
	//@ public normal_behaviour
	//@ ensures \result == orderID; 
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

}
