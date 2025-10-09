package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa identificativo generico. Più nello specifico, mappa il tipo molti-a-uno dei model Odoo.
 */
public class IdentifierDTO{
	/**
	 * Map del numero identificativo.
	 */
	private final Optional<Integer> num;
	/**
	 * Map del nome identificativo.
	 */
	private final Optional<String> name;
	
	/**
	 * Costruttore.
	 * @param array - un Array contenente due Object
	 */
	public IdentifierDTO(final Object[] array) {
		num = AttributeMapper.intify(array[0]);
		name = AttributeMapper.stringify(array[1]);
	}
	
	/**
	 * 
	 * @return oggetto Optional contenente Integer, altrimenti Optional.empty()
	 */
	public Optional<Integer> getNum() {
		return num;
	}
	
	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getName() {
		return name;
	}
	
	@Override
	public String toString() {
		return "FieldIdentifierDTO [num=" + num + ", name=" + name + "]";
	}
	
}
