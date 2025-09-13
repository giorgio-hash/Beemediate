package core.DTO;

import core.DTO.QuantityFieldValue;

public class Order {
	
	//struttura dati
	private /*@ spec_public @*/ Object data;
	
	//identificativo
	private /*@ spec_public @*/ final String orderID;
	
	//campi più importanti per controllo errori
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
	public Order(/*@ non_null*/Object d, String oID) {
		data = d;
		orderID = oID;
		quantity = QuantityFieldValue.NAN;
		customerNumber = articleNumber = quantityMeasure = deliveryLocationNumber = deliveryDate = deliveryDateContent = false;
	}

	//@ ensures \result == data;
	public /*@ pure @*/ Object getData() {
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

	//@ ensures \result == customerNumber;
	public /*@ pure @*/ boolean isCustomerNumber() {
		return customerNumber;
	}

	//@ assignable customerNumber;
	//@ ensures customerNumber == cn;
	public void setCustomerNumber(boolean cn) {
		customerNumber = cn;
	}

	//@ ensures \result == articleNumber;
	public /*@ pure @*/ boolean isArticleNumber() {
		return articleNumber;
	}

	//@ assignable articleNumber;
	//@ ensures articleNumber == an;
	public void setArticleNumber(boolean an) {
		articleNumber = an;
	}

	//@ ensures \result == quantityMeasure;
	public /*@ pure @*/ boolean isQuantityMeasure() {
		return quantityMeasure;
	}

	//@ assignable quantityMeasure;
	//@ensures quantityMeasure == qm;
	public void setQuantityMeasure(boolean qm) {
		quantityMeasure = qm;
	}

	//@ ensures \result == quantity;
	public /*@ pure @*/ QuantityFieldValue getQuantity() {
		return quantity;
	}

	//@ assignable quantity;
	//@ requires q != null;
	//@ ensures quantity == q;
	public void setQuantity(QuantityFieldValue q) {
		quantity = q;
	}

	//@ ensures \result == deliveryLocationNumber;
	public /*@ pure @*/ boolean isDeliveryLocationNumber() {
		return deliveryLocationNumber;
	}

	//@ assignable deliveryLocationNumber;
	//@ ensures deliveryLocationNumber == dln;
	public void setDeliveryLocationNumber(boolean dln) {
		deliveryLocationNumber = dln;
	}

	//@ ensures \result == deliveryDate;
	public /*@ pure @*/ boolean isDeliveryDate() {
		return deliveryDate;
	}

	//@ assignable deliveryDate;
	//@ ensures deliveryDate == dd;
	public void setDeliveryDate(boolean dd) {
		deliveryDate = dd;
	}

	//@ ensures \result == deliveryDateContent;
	public /*@ pure @*/ boolean isDeliveryDateContent() {
		return deliveryDateContent;
	}

	//@ assignable deliveryDateContent;
	//@ ensures deliveryDateContent == ddc;
	public void setDeliveryDateContent(boolean ddc) {
		deliveryDateContent = ddc;
	}
	
	//@ ensures \result == orderID; 
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

}
