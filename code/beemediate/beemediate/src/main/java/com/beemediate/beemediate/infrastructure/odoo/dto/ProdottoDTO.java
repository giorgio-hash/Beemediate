package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dettagli di un prodotto. I campi rimappano alcuni attributi richiesti al model <i>product.product</i> di Odoo.
 */
public class ProdottoDTO{
	
	/**
	 * Mapping di id
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di seller_ids
	 */
	private final Optional<Object[]> sellerIds;
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>product.product</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ProdottoDTO( final Map<String, Object> map) {
		
		id = AttributeMapper.intify(map.get("id"));
		
		sellerIds = AttributeMapper.toArray(map.get("seller_ids"));
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
	 * @return oggetto Optional contenente Object[], altrimenti Optional.empty()
	 */
	public Optional<Object[]> getSellerIds() {
		return sellerIds;
	}

	@Override
	public String toString() {
		return "ProdottoDTO [id=" + id + ", seller_ids=" + sellerIds + "]";
	}
	
	
	
}
