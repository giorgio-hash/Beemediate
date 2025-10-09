package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa gli articoli contenuti nel preventivo dell'ordine di acquisto. I campi rimappano alcuni attributi richiesti al model <i>purchase.order.line</i> di Odoo.
 */
public class ArticoloPreventivoDTO{
	
//	 {'id': 13,
//		  'order_id': [4, 'P00004'],
//		  'product_id': [6, 'schienale sedia'],
//		  'product_qty': 1.0}
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di order_id.
	 */
	private final IdentifierDTO orderId;
	/**
	 * Mapping di product_id.
	 */
	private final IdentifierDTO productId;
	/**
	 * Mapping di product_qty.
	 */
	private final Optional<Double> productQty;
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>purchase.order.line</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ArticoloPreventivoDTO( final Map<String, Object> map ) {
		
		id = AttributeMapper.intify( map.get("id") );
		
		orderId = new IdentifierDTO( (Object[]) map.get("order_id") );
		
		productId = new IdentifierDTO( (Object[]) map.get("product_id") );
		
		productQty = AttributeMapper.doublify( map.get("product_qty") );
	}

	/**
	 * 
	 * @return oggetto Optional contenente Integer, altrimenti Optional.empty()
	 */
	public Optional<Integer> getId() {
		return id;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo dell'ordine
	 */
	public IdentifierDTO getOrderId() {
		return orderId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo del prodotto associato a questo articolo.
	 */
	public IdentifierDTO getProductId() {
		return productId;
	}

	/**
	 * 
	 * @return oggetto Optional contenente Double, altrimenti Optional.empty()
	 */
	public Optional<Double> getProductQty() {
		return productQty;
	}

	@Override
	public String toString() {
		return "ArticoloPreventivoDTO [id=" + id + ", order_id=" + orderId + ", product_id=" + productId
				+ ", product_qty=" + productQty + "]";
	}

	
}
