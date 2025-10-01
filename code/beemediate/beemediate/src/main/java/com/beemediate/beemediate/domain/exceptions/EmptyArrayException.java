package com.beemediate.beemediate.domain.exceptions;

public class EmptyArrayException extends Exception {
	/*@ public normal_behaviour
	  @ requires msg!=null;
	  @ ensures super.getMessage() == msg;
	  @ pure
	  @*/	
	public EmptyArrayException(String msg) {
		super(msg);
	}
}
