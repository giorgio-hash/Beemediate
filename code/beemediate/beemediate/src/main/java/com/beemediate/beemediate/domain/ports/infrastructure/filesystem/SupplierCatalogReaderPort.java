package com.beemediate.beemediate.domain.ports.infrastructure.filesystem;

/**
 * Port per gestire l'adattatore che carica le informazioni dal catalogo fornitore.
 */
@SuppressWarnings("PMD.ImplicitFunctionalInterface")
public interface SupplierCatalogReaderPort {
	
	//@ public model instance String[] articleNumbers;
	
	/*@ public invariant articleNumbers!=null & 0<=articleNumbers.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant (\forall int i; 0<=i & i<articleNumbers.length; articleNumbers[i] != null ); @*/
	/*@ public invariant (\forall int i; 0<=i & i<articleNumbers.length; \typeof(articleNumbers[i]) == \type(String) ); @*/
	
	/**
	 * Restituisce Array di identificativi articolo
	 * @return String[] 
	 */
	/*@ public normal_behaviour
	  @ ensures \result==articleNumbers;
	  @*/
	/*@ spec_public pure @*/ String[] readArticleNumbers();

}
