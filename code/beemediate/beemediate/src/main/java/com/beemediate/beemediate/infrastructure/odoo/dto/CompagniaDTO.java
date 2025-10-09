package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dati della compagnia cliente che gestisce il CRM Odoo. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class CompagniaDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di company_registry.
	 */
	private final Optional<String> companyRegistry;
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>res.partner</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public CompagniaDTO( final Map<String, Object> map ) {
		id = AttributeMapper.intify( map.get("id") );
		companyRegistry = AttributeMapper.stringify( map.get("ref") ); 
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
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getCompanyRegistry() {
		return companyRegistry;
	}

	@Override
	public String toString() {
		return "CompagniaDTO [id=" + id + ", company_registry=" + companyRegistry + "]";
	}
	
	
}
