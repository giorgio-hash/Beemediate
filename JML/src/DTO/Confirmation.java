package DTO;

public class Confirmation {
	
	private /*@ spec_public @*/ Object data;
	
	/*@ public invariant data != null; @*/	
	
	//@ requires d != null;
	//@ ensures data == d;
	public Confirmation(Object d) {
		data = d;
	}

	//@ ensures \result == data;
	public Object getData() {
		return data;
	}

}
