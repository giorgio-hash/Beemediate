package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.HashMap;
import java.util.Optional;

public class ProdottoDTO extends XmlDTO{
	
	private Optional<Integer> id;
	private Optional<Object[]> seller_ids;
	
	public ProdottoDTO(HashMap<String, Object> map) {
		
		id = intify(map.get("id"));
		
		seller_ids = toArray(map.get("seller_ids"));
	}

	public Optional<Integer> getId() {
		return id;
	}

	public Optional<Object[]> getSeller_ids() {
		return seller_ids;
	}

	@Override
	public String toString() {
		return "ProdottoDTO [id=" + id + ", seller_ids=" + seller_ids + "]";
	}
	
	
	
}
