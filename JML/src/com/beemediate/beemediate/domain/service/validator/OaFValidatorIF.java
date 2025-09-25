package com.beemediate.beemediate.domain.service.validator;

import com.beemediate.beemediate.domain.pojo.order.Order;

public interface OaFValidatorIF {

	
	/*@ public normal_behaviour
	  @ assigns o.*;
	  @ requires o != null;
	  @ requires o.data != null;
	  @ requires o.quantity != null;
	  @ requires o.orderID != null;
	  @ requires \typeof(o) == \type(Order);
	  @ ensures \not_modified(o,o.data,o.quantity,o.orderID); 
	  @*/
	public void validate(Order o);

}