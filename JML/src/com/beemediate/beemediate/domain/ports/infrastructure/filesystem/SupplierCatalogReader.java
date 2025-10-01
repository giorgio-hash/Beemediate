package com.beemediate.beemediate.domain.ports.infrastructure.filesystem;

public interface SupplierCatalogReader {
	
	//@ public model instance String[] articleNumbers;
	
	/*@ public invariant articleNumbers!=null & 0<=articleNumbers.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant (\forall int i; 0<=i & i<articleNumbers.length; articleNumbers[i] != null ); @*/
	/*@ public invariant (\forall int i; 0<=i & i<articleNumbers.length; \typeof(articleNumbers[i]) == \type(String) ); @*/
	
	/*@ public normal_behaviour
	  @ ensures \result==articleNumbers;
	  @*/
	public /*@ pure @*/ String[] readArticleNumbers();

}
