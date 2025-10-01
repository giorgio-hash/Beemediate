package com.beemediate.beemediate.domain.exceptions;

public class UnreachableThresholdException extends Exception {
	
	/*@ public normal_behaviour
	  @ requires msg!=null;
	  @ ensures super.getMessage() == msg;
	  @ pure
	  @*/
	public UnreachableThresholdException(String msg) {
		super(msg);
	}
}
