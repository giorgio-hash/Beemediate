package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class CompagniaDTO extends XmlDTO{
	private Optional<Integer> id;
	private Optional<String> company_registry;
	
	public CompagniaDTO( Map<String, Object> map ) {
		id = intify( map.get("id") );
		company_registry = stringify( map.get("ref") ); 
	}

	public Optional<Integer> getId() {
		return id;
	}

	public Optional<String> getCompany_registry() {
		return company_registry;
	}

	@Override
	public String toString() {
		return "CompagniaDTO [id=" + id + ", company_registry=" + company_registry + "]";
	}
	
	
}
