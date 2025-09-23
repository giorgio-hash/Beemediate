package domain.core.dto;

public class Confirmation {
	
	private /*@ spec_public @*/ Object data;
	
	//identificativo
	private /*@ spec_public @*/ final String orderID;
	
	/*@ public invariant data != null; @*/
	/*@ public invariant orderID != null; @*/
	
	//@ requires d != null & oID!=null;
	//@ ensures data == d & orderID == oID;
	//@ pure
	public Confirmation(Object d, String oID) {
		data = d;
		orderID = oID;
	}

	//@ ensures \result == data;
	public /*@ pure @*/ Object getData() {
		return data;
	}
	
	//@ ensures \result == orderID;
	public /*@ pure @*/ String getOrderID() {
		return orderID;
	}

}
