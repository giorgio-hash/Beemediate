package core.DTO;

public class Confirmation {
	
	private /*@ spec_public @*/ Object data;
	
	/*@ public invariant data != null; @*/	
	
	//@ requires d != null;
	//@ ensures data == d;
	//@ pure
	public Confirmation(Object d) {
		data = d;
	}

	//@ ensures \result == data;
	public /*@ pure @*/ Object getData() {
		return data;
	}

}
