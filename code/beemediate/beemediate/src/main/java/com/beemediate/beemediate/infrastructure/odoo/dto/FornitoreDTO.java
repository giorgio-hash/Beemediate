package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa informazioni di contatto fornitore. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class FornitoreDTO{
	
	/**
	 * Mapping di name
	 */
	private final Optional<String> name;
	/**
	 * Mapping di ref
	 */
	private final Optional<String> codiceAzienda;
	/**
	 * Mapping di id
	 */
	private final Optional<Integer> id;
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>res.partner</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public FornitoreDTO(final Map<String, Object> map) {
		name = AttributeMapper.stringify(map.get("name"));
		codiceAzienda = AttributeMapper.stringify(map.get("ref"));
		id = AttributeMapper.intify(map.get("id"));
	}
	
	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getName() {
		return name;
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
	public Optional<String>  getCodiceAzienda() {
		return codiceAzienda;
	}
	
	@Override
	public String toString() {
		return "FornitoreDTO [name=" + name + ", codiceAzienda=" + codiceAzienda + ", id=" + id
				+ "]";
	}
	
	

}
