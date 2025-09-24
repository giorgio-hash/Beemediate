package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class ContattoConsegnaDTO extends XmlDTO{
	
	private Optional<Integer> id;
	private FieldIdentifierDTO partner_id;
	
	public ContattoConsegnaDTO( Map<String, Object> map ) {
		id = intify( map.get("id") );
		partner_id = new FieldIdentifierDTO( (Object[]) map.get("partner_id") );
	}

	public Optional<Integer> getId() {
		return id;
	}

	public FieldIdentifierDTO getPartner_id() {
		return partner_id;
	}

	@Override
	public String toString() {
		return "ContattoConsegnaDTO [id=" + id + ", partner_id=" + partner_id + "]";
	}
	
	
}
