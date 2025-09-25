package com.beemediate.beemediate.domain.service.validator.impl;

import org.jmlspecs.annotation.CodeBigintMath;

import com.beemediate.beemediate.domain.exceptions.EmptyArrayException;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.pojo.order.QuantityFieldValue;
import com.beemediate.beemediate.domain.ports.infrastructure.filesystem.SupplierCatalogReader;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;
import com.beemediate.beemediate.domain.utils.StringHandler;

public class OaFValidator implements OaFValidatorIF{
	

	/*@ spec_public */ final String customerNumber = "3024005150";
	/*@ spec_public */ final QuantityFieldValue quantity = QuantityFieldValue.FLOAT_WITH_DOT;
	/*@ spec_public */ final char quantityMeasure = 'M';
	private /*@ spec_public */ final String[] deliveryLocationNumber = {"3024005150","30901505150"};
	private /*@ spec_public */ final String[] articleNumbers;
	

	/*@ public invariant 0<articleNumbers.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant (\forall int i; 0<=i<articleNumbers.length; articleNumbers[i]!=null); @*/
	/*@ public invariant (\forall int i; 0<=i<articleNumbers.length; 0<articleNumbers[i].length()<=Integer.MAX_VALUE); @*/
	
	/*@ public normal_behaviour
	  @ requires catalog!=null;
	  @ requires catalog.articleNumbers.length>0;
	  @ requires (\forall int i; 0<=i<catalog.articleNumbers.length; 0<catalog.articleNumbers[i].length()<=Integer.MAX_VALUE);
	  @ requires (\forall int i; 0<=i<catalog.articleNumbers.length; \typeof(catalog.articleNumbers[i])==\type(String));
	  @ ensures customerNumber!=null;
	  @ ensures quantity != null;
	  @ ensures quantityMeasure == 'M';
	  @ ensures deliveryLocationNumber!=null & deliveryLocationNumber.length==2;
	  @ ensures articleNumbers!=null & articleNumbers.length>0;
	  @
	  @ also public exceptional_behaviour
	  @ requires catalog!=null;
	  @ requires catalog.articleNumbers.length==0;  
	  @ signals_only EmptyArrayException;
	  @*/
	@CodeBigintMath
	public /*@ pure*/ OaFValidator (SupplierCatalogReader catalog) throws EmptyArrayException {
		String[] rows = catalog.readArticleNumbers(); 
		if(rows.length == 0)
			throw new EmptyArrayException("ID articoli non trovati.");
		articleNumbers = rows;
	}
	

	@Override
	public void validate(Order o) {

	}
	
	/*@ public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires ost.header.buyerID.length()!=customerNumber.length() | ost.header.buyerIDRef.length()!=customerNumber.length();
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires ost.header.buyerID.length()==ost.header.buyerIDRef.length() & ost.header.buyerID.length()==customerNumber.length();
	  @ requires (\exists int i; 0<=i<ost.header.buyerID.length(); ost.header.buyerIDRef.charAt(i) != customerNumber.charAt(i) | ost.header.buyerIDRef.charAt(i) != customerNumber.charAt(i) );
	  @ ensures  !\result;
	  @
	  @ also public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires ost.header.buyerID.length()>0;
	  @ requires ost.header.buyerID.length()==ost.header.buyerIDRef.length() & ost.header.buyerID.length()==customerNumber.length();
	  @ requires (\forall int i; 0<=i<ost.header.buyerID.length(); ost.header.buyerIDRef.charAt(i) == customerNumber.charAt(i));
	  @ requires (\forall int i; 0<=i<=ost.header.buyerIDRef.length(); ost.header.buyerIDRef.charAt(i) == customerNumber.charAt(i) );
	  @ requires (\forall int i; 0<=i<=ost.header.buyerIDRef.length(); ost.header.buyerIDRef.charAt(i) == ost.header.buyerID.charAt(i) );
	  @ ensures  \result;
	  @*/
	@CodeBigintMath
	private /*@ spec_public pure @*/ boolean validateCustomerNumber( /*@ non_null @*/ OrderStructure ost) {
		
		return StringHandler.equals(ost.getHeader().getBuyerID(), ost.getHeader().getBuyerIDRef())
				&& StringHandler.equals(ost.getHeader().getBuyerID(), this.customerNumber);
	}
	
	/*@ public normal_behaviour
	  @ requires articleNumbers!=null;
	  @ requires ost!=null;
	  @ requires ost.itemList!=null;
	  @ requires ost.itemList.length>0;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i] != null);
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; \typeof(ost.itemList[i]) == \type(OrderItem) );
	  @ requires \elemtype(\typeof(ost.itemList)) == \type(OrderItem);
	  @ requires (ost.itemList!=null & ost.orderSummary!=null) ==> ost.orderSummary.totalItemNum == ost.itemList.length;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i].supplierID!=null & ost.itemList[i].supplierID.length()>0);
	  @ ensures \result <==> (\forall int i; 0<=i<ost.itemList.length; isInCatalog(ost.itemList[i].supplierID) );
	  @*/
	@CodeBigintMath
	private /*@ spec_public pure @*/ boolean validateArticleNumber(/*@ non_null @*/ OrderStructure ost) {
		
		boolean found = true;
		
		/*@ loop_writes found;
		  @ loop_invariant \count < ost.itemList.length ==> il!=null;
		  @ loop_invariant 0<=\count<=ost.itemList.length;
		  @ loop_invariant found <==> (\forall int j; 0<=j<\count; isInCatalog(ost.itemList[j].supplierID) );
		  @ decreases ost.itemList.length - \count;
		  @*/
		for(OrderItem il : ost.getItemList()) {
			if( !isInCatalog(il.getSupplierID()) ) {
				found = false;
				break;
			}
		}
		
		return found;
	}
	
	/*@ public normal_behaviour
	  @ requires artNum!=null & artNum.length()>0;
	  @ requires articleNumbers!=null;
	  @ ensures \result <==> (\exists int i; 0<=i<articleNumbers.length; StringHandler.equals(articleNumbers[i],artNum)  );
	  @*/
	private /*@ spec_public pure @*/ boolean isInCatalog(/*@ non_null @*/ String artNum) {
		
		boolean inCatalog = false;
		
		/*@ loop_writes inCatalog;
		  @ loop_invariant \count < articleNumbers.length ==> a!=null;
		  @ loop_invariant 0<=\count<=articleNumbers.length;
		  @ loop_invariant !inCatalog <==> (\forall int j; 0<=j<\count; !StringHandler.equals(articleNumbers[j], artNum) );
		  @ decreases articleNumbers.length - \count;
		  @*/
		for(String a : articleNumbers) {
			if( StringHandler.equals(a, artNum) ) {
				inCatalog = true;
				break;
			}
		}
		return inCatalog;
	}

}
