package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dettagli relativi al luogo di consegna. I campi rimappano alcuni attributi richiesti al model <i>stock.warehouse</i> di Odoo.
 */
public class ContattoConsegnaDTO{
	
	/**
	 * Mapping di id.
	 */
	private Optional<Integer> id;
	/**
	 * Mapping di partner_id.
	 */
	private IdentifierDTO partnerId;
	
	/**
	 * 
	 * @param map - Map contente una tupla del model <i>stock.warehouse</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ContattoConsegnaDTO( final Map<String, Object> map ) {
		id = AttributeMapper.intify( map.get("id") );
		partnerId = new IdentifierDTO( (Object[]) map.get("partner_id") );
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
	 * @return oggetto IdentifierDTO con identificativo della compagnia.
	 */
	public IdentifierDTO getPartnerId() {
		return partnerId;
	}

	@Override
	public String toString() {
		return "ContattoConsegnaDTO [id=" + id + ", partner_id=" + partnerId + "]";
	}
	
	
}
