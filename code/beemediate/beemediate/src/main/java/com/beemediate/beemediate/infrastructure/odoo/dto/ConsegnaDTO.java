package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class ConsegnaDTO extends XmlDTO{
	
	private Optional<Integer> id;
	private FieldIdentifierDTO warehouse_id;
	
	public ConsegnaDTO ( Map<String, Object> map ) {
		
		id = intify( map.get("id") );
		
		warehouse_id = new FieldIdentifierDTO( (Object[]) map.get("warehouse_id") );
	}

	public Optional<Integer> getId() {
		return id;
	}

	public FieldIdentifierDTO getWarehouse_id() {
		return warehouse_id;
	}
	
	@Override
	public String toString() {
		return "ConsegnaDTO [id=" + id + ", warehouse_id=" + warehouse_id + "]";
	}	

}
