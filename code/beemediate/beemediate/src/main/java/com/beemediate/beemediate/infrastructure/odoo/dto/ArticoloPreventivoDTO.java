package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class ArticoloPreventivoDTO extends XmlDTO{
	
//	 {'id': 13,
//		  'order_id': [4, 'P00004'],
//		  'product_id': [6, 'schienale sedia'],
//		  'product_qty': 1.0}
	
	private Optional<Integer> id;
	private FieldIdentifierDTO order_id;
	private FieldIdentifierDTO product_id;
	private Optional<Double> product_qty;
	
	public ArticoloPreventivoDTO( Map<String, Object> map ) {
		
		id = intify( map.get("id") );
		
		order_id = new FieldIdentifierDTO( (Object[]) map.get("order_id") );
		
		product_id = new FieldIdentifierDTO( (Object[]) map.get("product_id") );
		
		product_qty = doublify( map.get("product_qty") );
	}

	public Optional<Integer> getId() {
		return id;
	}

	public FieldIdentifierDTO getOrder_id() {
		return order_id;
	}

	public FieldIdentifierDTO getProduct_id() {
		return product_id;
	}

	public Optional<Double> getProduct_qty() {
		return product_qty;
	}

	@Override
	public String toString() {
		return "ArticoloPreventivoDTO [id=" + id + ", order_id=" + order_id + ", product_id=" + product_id
				+ ", product_qty=" + product_qty + "]";
	}

	
}
