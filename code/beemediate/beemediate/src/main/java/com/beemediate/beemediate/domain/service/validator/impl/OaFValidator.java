package com.beemediate.beemediate.domain.service.validator.impl;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

//import org.jmlspecs.annotation.CodeBigintMath;

//import org.jmlspecs.annotation.SkipEsc;

import com.beemediate.beemediate.domain.exceptions.EmptyArrayException;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.pojo.order.QuantityFieldValue;
import com.beemediate.beemediate.domain.ports.infrastructure.filesystem.SupplierCatalogReaderPort;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;
import com.beemediate.beemediate.domain.utils.StringHandler;

/**
 * Classe incaricata di verificare la OrderStructure per confermare che le informazioni contenute rispettino i vincoli richiesti dal sistema fornitore.
 */
@Service
public class OaFValidator implements OaFValidatorIF{
	

	/***Numero cliente corretto*/
	private /*@ spec_public */ final String customerNumber = "3024005150";
	/***Formato corretto del valore di quantità di ogni articolo.*/
	private /*@ spec_public */ final QuantityFieldValue quantity = QuantityFieldValue.FLOAT_WITH_DOT;
	/***Unità di misura corretta per il valore di quantità di ogni articolo.*/
	private /*@ spec_public */ final char quantityMeasure = 'M';
	/***Numeri corretti di località di consegna*/
	private /*@ spec_public */ final String[] deliveryLocationNumber = {"3024005150","30901505150"};
	/***Elenco numeri articolo da catalogo fornitore.*/
	private /*@ spec_public */ final String[] articleNumbers;
	

	/*@ public invariant 0<articleNumbers.length<=Integer.MAX_VALUE; @*/
	/*@ public invariant (\forall int i; 0<=i<articleNumbers.length; articleNumbers[i]!=null); @*/
	/*@ public invariant (\forall int i; 0<=i<articleNumbers.length; 0<articleNumbers[i].length()<=Integer.MAX_VALUE); @*/
	
	/**
	 * Costruttore
	 * @param catalog - adattatore SupplierCatalogReaderPort
	 * @throws EmptyArrayException se l'elenco dei numeri articolo risulta vuoto
	 */
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
//	@CodeBigintMath
	@Autowired
	public /*@ pure*/ OaFValidator (final SupplierCatalogReaderPort catalog) throws EmptyArrayException {
		String[] rows = catalog.readArticleNumbers(); 
		if(rows.length == 0)
			throw new EmptyArrayException("ID articoli non trovati.");
		articleNumbers = rows;
	}
	
//	@SkipEsc
	@Override
	public void validate(/*@ non_null @*/final Order o) {
		
		OrderStructure ost = o.getData();
			
		o.setCustomerNumber( this.validateCustomerNumber( ost ) );
		o.setArticleNumber( this.validateArticleNumber( ost ) );
		o.setQuantityMeasure( this.validateQuantityMeasure( ost ) );
		o.setQuantity( this.validateQuantity( ost ) );
		o.setDeliveryLocationNumber( this.validateDeliveryLocationNumber( ost ) );
		o.setDeliveryDate( this.validateDeliveryDate( ost) );
		o.setDeliveryDateContent( this.validateDeliveryDateContent( ost ) );
	}
	
	/**
	 * Verifica che buyerID, buyerIDRef e customerNumber abbiano lo stesso valore.
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
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
//	@CodeBigintMath
	private /*@ spec_public pure @*/ boolean validateCustomerNumber( /*@ non_null @*/final OrderStructure ost) {
		
		return StringHandler.equals(ost.getHeader().getBuyerID(), ost.getHeader().getBuyerIDRef())
				&& StringHandler.equals(ost.getHeader().getBuyerID(), this.customerNumber);
	}
	
	/**
	 * Verifica che i campi deliveryID, deliveryIDRef ed almeno una delle deliveryLocationNumver abbiano lo stesso valore.
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
	/*@ public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires deliveryLocationNumber!=null & deliveryLocationNumber.length==2;
	  @ requires (\forall int i; 0<=i<2; deliveryLocationNumber[i]!=null & deliveryLocationNumber[i].length()>0);
	  @ requires (\forall int i; 0<=i<2; ost.header.deliveryID.length()!=deliveryLocationNumber[i].length())
	  @				| (\forall int i; 0<=i<2; ost.header.deliveryIDRef.length()!=deliveryLocationNumber[i].length());
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires deliveryLocationNumber!=null & deliveryLocationNumber.length==2;
	  @ requires (\forall int i; 0<=i<2; deliveryLocationNumber[i]!=null & deliveryLocationNumber[i].length()>0);
	  @	requires ost.header.deliveryID.length() != ost.header.deliveryIDRef.length();
	  @ ensures  !\result;
	  @
	  @
	  @ also public normal_behaviour
	  @ requires ost.header!=null;
	  @ requires deliveryLocationNumber!=null & deliveryLocationNumber.length==2;
	  @ requires (\forall int i; 0<=i<2; deliveryLocationNumber[i]!=null & deliveryLocationNumber[i].length()>0);
	  @ requires (\exists int i; 0<=i<2; ost.header.deliveryID.length()==deliveryLocationNumber[i].length()
	  @										& (\forall int j; 0<=j<ost.header.deliveryID.length(); ost.header.deliveryID.charAt(j)==deliveryLocationNumber[i].charAt(j) ));
	  @	requires ost.header.deliveryID.length() == ost.header.deliveryIDRef.length();
	  @ requires (\forall int j; 0<=j<ost.header.deliveryID.length(); ost.header.deliveryID.charAt(j)==ost.header.deliveryIDRef.charAt(j) );
	  @ ensures  \result;
	  @*/
//	@CodeBigintMath
	private /*@ spec_public pure @*/ boolean validateDeliveryLocationNumber( /*@ non_null @*/final OrderStructure ost) {
		
		return StringHandler.equals(ost.getHeader().getDeliveryID(), ost.getHeader().getDeliveryIDRef())
				&& (StringHandler.equals(ost.getHeader().getDeliveryID(), this.deliveryLocationNumber[0])
						|| StringHandler.equals(ost.getHeader().getDeliveryID(), this.deliveryLocationNumber[1]));
	}
	
	/**
	 * Verifica che ogni OrderItem in ost.getItemList() abbia supplierID con valore presente in articleNumbers.
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
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
//	@CodeBigintMath
	private /*@ spec_public pure @*/ boolean validateArticleNumber(/*@ non_null @*/final OrderStructure ost) {
		
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
	
	/**
	 * 
	 * @param artNum - String
	 * @return <i>true</i> se artNum è presente in articleNumbers
	 */
	/*@ public normal_behaviour
	  @ requires artNum!=null & artNum.length()>0;
	  @ requires articleNumbers!=null;
	  @ ensures \result <==> (\exists int i; 0<=i<articleNumbers.length; StringHandler.equals(articleNumbers[i],artNum)  );
	  @*/
	private /*@ spec_public pure @*/ boolean isInCatalog(/*@ non_null @*/final String artNum) {
		
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
	
	/**
	 * Per ogni OrderItem presente in OrderStructure, quantityMeasure dev'essere uguale a 'M'.
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
	/*@ public normal_behaviour
	  @ requires articleNumbers!=null;
	  @ requires ost!=null;
	  @ requires ost.itemList!=null;
	  @ requires ost.itemList.length>0;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i] != null);
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; \typeof(ost.itemList[i]) == \type(OrderItem) );
	  @ requires \elemtype(\typeof(ost.itemList)) == \type(OrderItem);
	  @ requires (ost.itemList!=null & ost.orderSummary!=null) ==> ost.orderSummary.totalItemNum == ost.itemList.length;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i].orderUnit!=null);
	  @ ensures !\result <==> (\exists int i; 0<=i<ost.itemList.length; ost.itemList[i].orderUnit.length()!=1 | ost.itemList[i].orderUnit.charAt(0)!=quantityMeasure  );
	  @*/
	private /*@ spec_public pure @*/ boolean validateQuantityMeasure(/*@ non_null @*/final OrderStructure ost) {
		
		boolean rightMeasureUnit = true;
		
		/*@ loop_writes rightMeasureUnit;
		  @ loop_invariant \count < ost.itemList.length ==> il!=null;
		  @ loop_invariant 0<=\count<=ost.itemList.length;
		  @ loop_invariant rightMeasureUnit <==> (\forall int j; 0<=j<\count; ost.itemList[j].orderUnit.length()==1 & ost.itemList[j].orderUnit.charAt(0) == quantityMeasure );
		  @ decreases ost.itemList.length - \count;
		  @*/
		for(OrderItem il : ost.getItemList()) {
			if( il.getOrderUnit().length()!=1 || il.getOrderUnit().charAt(0) != quantityMeasure ) {
				rightMeasureUnit = false;
				break;
			}
		}
		
		return rightMeasureUnit;
	}
	
	/**
	 * Verifica la forma del campo quantity di ogni OrderItem.
	 * <ul>
	 * <li>Alla prima occorrenza di un campo quantity non numerico, restituisce <i>QuantityFieldValue.NAN</i>;</li>
	 * <li>Alla prima occorrenza di un campo quantity contenente un numero a virgola mobile ma con "," al posto di ".", restituisce <i>QuantityFieldValue.FLOAT_WITH_COMMA</i>.</li>
	 * </ul>
	 * Se i precedenti due eventi non si verificano:
	 * <ul>
	 * <li>Se esiste almeno un campo quantity numerico senza virgola mobile, restituisce <i>QuantityFieldValue.INTEGER</i>;</li>
	 * <li>Altrimenti, restituisce <i>QuantityFieldValue.FLOAT_WITH_DOT</i>.</li>
	 * </ul>
	 * @param ost - OrderStructure
	 * @return valore enum QuantityFieldValue
	 */
	/*@ public normal_behaviour
	  @ requires ost.itemList!=null;
	  @ requires ost.itemList.length>0;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i] != null);
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; \typeof(ost.itemList[i]) == \type(OrderItem) );
	  @ requires \elemtype(\typeof(ost.itemList)) == \type(OrderItem);
	  @ requires (ost.orderSummary!=null) ==> ost.orderSummary.totalItemNum == ost.itemList.length;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i].quantity!=null & ost.itemList[i].quantity.length()>=0);
	  @ ensures \result==QuantityFieldValue.FLOAT_WITH_DOT | \result==QuantityFieldValue.INTEGER | \result==QuantityFieldValue.FLOAT_WITH_COMMA | \result==QuantityFieldValue.NAN;
	  @*/
//	@CodeBigintMath
	private /*@ spec_public pure @*/ QuantityFieldValue validateQuantity(/*@ non_null @*/final OrderStructure ost) {
		
		
		QuantityFieldValue qfv = QuantityFieldValue.FLOAT_WITH_DOT;
		
		/*@ loop_writes \nothing;
		  @ loop_invariant 0<=\count<=ost.itemList.length;
		  @ loop_invariant \count < ost.itemList.length ==> (il!=null & il.quantity.length()>=0);
		  @ loop_invariant (qfv==QuantityFieldValue.FLOAT_WITH_DOT & \count>0) ==> (\forall int i; 0<=i<\count; StringHandler.isDouble(ost.itemList[i].quantity) );
		  @ loop_invariant (qfv==QuantityFieldValue.INTEGER & \count>0) ==> (\exists int i; 0<=i<\count; StringHandler.isInteger(ost.itemList[i].quantity));
		  @ loop_invariant qfv==QuantityFieldValue.FLOAT_WITH_COMMA ==> (!StringHandler.isDouble(il.quantity) & StringHandler.containsChar(il.quantity,',') );
		  @ loop_invariant qfv==QuantityFieldValue.NAN ==> (!StringHandler.isDouble(il.quantity) & !StringHandler.containsChar(il.quantity,',') );
		  @ decreases ost.itemList.length - \count;
		  @*/
		for(OrderItem il : ost.getItemList()) {
			
			if(StringHandler.isDouble(il.getQuantity()))
				continue;
			else if(StringHandler.isInteger(il.getQuantity())) {
				qfv = QuantityFieldValue.INTEGER;
				continue;
			} else {
				if(StringHandler.containsChar(il.getQuantity(),','))
					qfv = QuantityFieldValue.FLOAT_WITH_COMMA;
				else
					qfv = QuantityFieldValue.NAN;
				
				return qfv;
			} 
		}
		
		return qfv;
	}
	
	/**
	 * Verifica che startDate, orderDate ed endDate siano delle stringhe rappresentanti un timestamp nel formato "yyyy-MM-dd HH:mm:ss".
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
	/*@ public normal_behaviour
	  @ requires ost.itemList!=null;
	  @ requires ost.itemList.length>0;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i] != null);
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; \typeof(ost.itemList[i]) == \type(OrderItem) );
	  @ requires \elemtype(\typeof(ost.itemList)) == \type(OrderItem);
	  @ requires (ost.orderSummary!=null) ==> ost.orderSummary.totalItemNum == ost.itemList.length;
	  @ requires ost.header!=null;
	  @ ensures !\result <==> (!StringHandler.isDateTime(ost.header.startDate) | !StringHandler.isDateTime(ost.header.orderDate) | !StringHandler.isDateTime(ost.header.endDate));
	  @*/
	private /*@ spec_public pure @*/ boolean validateDeliveryDateContent(/*@ non_null@*/final OrderStructure ost) {
		return ost.getHeader().getStartDate()!=null && StringHandler.isDateTime(ost.getHeader().getStartDate())
				&& ost.getHeader().getOrderDate()!=null && StringHandler.isDateTime(ost.getHeader().getOrderDate())
				&& ost.getHeader().getEndDate()!=null && StringHandler.isDateTime(ost.getHeader().getEndDate());
	}
	
	/**
	 * Verifica che siano rispettate tutte le seguenti condizioni:
	 * <ul>
	 * <li>startDate, orderDate ed endDate sono delle stringhe rappresentanti un timestamp nel formato "yyyy-MM-dd HH:mm:ss";</li>
	 * <li>startDate precede temporalmente endDate;</li>
	 * <li>orderDate e endDate coincidono;</li>
	 * </ul>
	 * @param ost - OrderStructure
	 * @return <i>true</i> se condizione rispettata
	 */
	/*@ public normal_behaviour
	  @ requires ost.itemList!=null;
	  @ requires ost.itemList.length>0;
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; ost.itemList[i] != null);
	  @ requires (\forall int i; 0<=i & i<ost.itemList.length; \typeof(ost.itemList[i]) == \type(OrderItem) );
	  @ requires \elemtype(\typeof(ost.itemList)) == \type(OrderItem);
	  @ requires (ost.orderSummary!=null) ==> ost.orderSummary.totalItemNum == ost.itemList.length;
	  @ requires ost.header!=null;
	  @ ensures \result ==> (StringHandler.isDateTime(ost.header.startDate) & StringHandler.isDateTime(ost.header.orderDate) & StringHandler.isDateTime(ost.header.endDate));
	  @ ensures \result ==> (\forall int i; 1<=i<ost.header.startDate.length() & i!=4 & i!=7 & i!=10 & i!=13 & i!=16; ost.header.startDate.charAt(i)<=ost.header.endDate.charAt(i) );
	  @ ensures \result ==> (\forall int i; 1<=i<ost.header.startDate.length() & i!=4 & i!=7 & i!=10 & i!=13 & i!=16; ost.header.orderDate.charAt(i)==ost.header.endDate.charAt(i) );
	  @*/
	private /*@ spec_public pure @*/ boolean validateDeliveryDate(/*@ non_null @*/final OrderStructure ost) {
		return validateDeliveryDateContent(ost) 
				&& StringHandler.beforeOrEqualDateTime(ost.getHeader().getStartDate(), ost.getHeader().getEndDate())
				&& StringHandler.equals(ost.getHeader().getOrderDate(), ost.getHeader().getEndDate());
	}

}
