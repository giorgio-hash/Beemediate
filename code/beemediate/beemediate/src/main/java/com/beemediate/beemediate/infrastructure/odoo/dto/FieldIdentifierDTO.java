package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Optional;

public class FieldIdentifierDTO extends XmlDTO{
	private Optional<Integer> num;
	private Optional<String> name;
	
	
	public FieldIdentifierDTO(Object[] array) {
		num = intify(array[0]);
		name = stringify(array[1]);
	}
	
	public Optional<Integer> getNum() {
		return num;
	}
	public Optional<String> getName() {
		return name;
	}
	@Override
	public String toString() {
		return "FieldIdentifierDTO [num=" + num + ", name=" + name + "]";
	}
	
}
