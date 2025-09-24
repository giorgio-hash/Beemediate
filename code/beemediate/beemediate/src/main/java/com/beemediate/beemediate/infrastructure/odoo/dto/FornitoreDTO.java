package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class FornitoreDTO extends XmlDTO{
	
	
	private Optional<String> name;
	private Optional<String> codiceAzienda;
	private Optional<Integer> id;
	
	
	public FornitoreDTO(Map<String, Object> map) {
		name = stringify(map.get("name"));
		codiceAzienda = stringify(map.get("ref"));
		id = intify(map.get("id"));
	}
	
	public Optional<String> getName() {
		return name;
	}

	public Optional<Integer> getId() {
		return id;
	}
	public Optional<String>  getCodiceAzienda() {
		return codiceAzienda;
	}
	@Override
	public String toString() {
		return "FornitoreDTO [name=" + name + ", codiceAzienda=" + codiceAzienda + ", id=" + id
				+ "]";
	}
	
	

}
