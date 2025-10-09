package com.beemediate.beemediate.domain.service.validator;

import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Interfaccia del OaFValidator.
 */
@SuppressWarnings("PMD.ImplicitFunctionalInterface")
public interface OaFValidatorIF {

	/**
	 * Dato un Order, modifica i flag a seguito della verifica della OrderStructure.
	 * @param o - Order
	 */
	/*@ public normal_behaviour
	  @ assigns o.*;
	  @ requires o != null;
	  @ requires o.data != null;
	  @ requires o.quantity != null;
	  @ requires o.orderID != null;
	  @ requires \typeof(o) == \type(Order);
	  @ ensures \not_modified(o,o.data,o.orderID);
	  @ ensures o.quantity!=null; 
	  @*/
	/*@ soec_public @*/ void validate(final Order o);

}