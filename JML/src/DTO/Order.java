package DTO;

import DTO.QuantityFieldValue;

public class Order {
	
	//struttura dati
	private /*@ spec_public @*/ Object data;
	
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
	
	/*@ requires d != null;
	  @ ensures data == d && quantity == QuantityFieldValue.NAN
	  @						&& !customerNumber && !articleNumber && !quantityMeasure 
	  @						&& !deliveryLocationNumber && !deliveryDate && !deliveryDateContent;						
	  @ pure
	  @*/
	public Order(Object d) {
		data = d;
		quantity = QuantityFieldValue.NAN;
		customerNumber = articleNumber = quantityMeasure = deliveryLocationNumber = deliveryDate = deliveryDateContent = false;
	}

	//@ ensures \result == data;
	public Object getData() {
		return data;
	}

	//@ ensures \result == (!articleNumber | !quantityMeasure | (deliveryDate & !deliveryDateContent) );
	public boolean hasContentError() {
		return !(articleNumber && quantityMeasure && (!deliveryDate || deliveryDateContent));
	}

	//@ requires quantity != null;
	//@ ensures \result == (!customerNumber | !deliveryLocationNumber | !deliveryDate | quantity != QuantityFieldValue.FLOAT_WITH_DOT);
	public boolean hasOpenTransError() {
		return !(customerNumber && deliveryLocationNumber && deliveryDate && quantity == QuantityFieldValue.FLOAT_WITH_DOT);
	}

	//@ ensures \result == customerNumber;
	public boolean isCustomerNumber() {
		return customerNumber;
	}

	//@ assignable customerNumber;
	//@ ensures customerNumber == cn;
	public void setCustomerNumber(boolean cn) {
		customerNumber = cn;
	}

	//@ ensures \result == articleNumber;
	public boolean isArticleNumber() {
		return articleNumber;
	}

	//@ assignable articleNumber;
	//@ ensures articleNumber == an;
	public void setArticleNumber(boolean an) {
		articleNumber = an;
	}

	//@ ensures \result == quantityMeasure;
	public boolean isQuantityMeasure() {
		return quantityMeasure;
	}

	//@ assignable quantityMeasure;
	//@ensures quantityMeasure == qm;
	public void setQuantityMeasure(boolean qm) {
		quantityMeasure = qm;
	}

	//@ ensures \result == quantity;
	public QuantityFieldValue getQuantity() {
		return quantity;
	}

	//@ assignable quantity;
	//@ requires q != null;
	//@ ensures quantity == q;
	public void setQuantity(QuantityFieldValue q) {
		quantity = q;
	}

	//@ ensures \result == deliveryLocationNumber;
	public boolean isDeliveryLocationNumber() {
		return deliveryLocationNumber;
	}

	//@ assignable deliveryLocationNumber;
	//@ ensures deliveryLocationNumber == dln;
	public void setDeliveryLocationNumber(boolean dln) {
		deliveryLocationNumber = dln;
	}

	//@ ensures \result == deliveryDate;
	public boolean isDeliveryDate() {
		return deliveryDate;
	}

	//@ assignable deliveryDate;
	//@ ensures deliveryDate == dd;
	public void setDeliveryDate(boolean dd) {
		deliveryDate = dd;
	}

	//@ ensures \result == deliveryDateContent;
	public boolean isDeliveryDateContent() {
		return deliveryDateContent;
	}

	//@ assignable deliveryDateContent;
	//@ ensures deliveryDateContent == ddc;
	public void setDeliveryDateContent(boolean ddc) {
		deliveryDateContent = ddc;
	}
	

}
