package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class ProdottoFornitoreDTO extends XmlDTO{
	
//	 {'id': 4,
//		  'product_id': [4, 'tavola per sedia'],
//		  'sequence': 1,
//		  'product_name': False,
//		  'product_code': False,
//		  'partner_id': [8, 'GEALAN']}
	
	private Optional<Integer> id;
	private FieldIdentifierDTO product_id;
	private Optional<Integer> sequence;
	private Optional<String> product_name;
	private Optional<String> product_code;
	private FieldIdentifierDTO partner_id;
	private FieldIdentifierDTO product_uom_id;
	
	
	public ProdottoFornitoreDTO( Map<String, Object> map ) {
		
		id = intify( map.get("id") );
		
		product_id = new FieldIdentifierDTO( (Object[]) map.get("product_id") );
		
		sequence = intify( map.get("sequence") );
		
		product_name = stringify( map.get("product_name") );
		
		product_code = stringify( map.get("product_code") );
		
		partner_id = new FieldIdentifierDTO( (Object[]) map.get("partner_id"));
		
		product_uom_id = new FieldIdentifierDTO( (Object[]) map.get("product_uom_id") );
	}


	public Optional<Integer> getId() {
		return id;
	}


	public FieldIdentifierDTO getProduct_id() {
		return product_id;
	}


	public Optional<Integer> getSequence() {
		return sequence;
	}


	public Optional<String> getProduct_name() {
		return product_name;
	}


	public Optional<String> getProduct_code() {
		return product_code;
	}


	public FieldIdentifierDTO getPartner_id() {
		return partner_id;
	}


	public FieldIdentifierDTO getProduct_uom_id() {
		return product_uom_id;
	}


	@Override
	public String toString() {
		return "ProdottoFornitoreDTO [id=" + id + ", product_id=" + product_id + ", sequence=" + sequence
				+ ", product_name=" + product_name + ", product_code=" + product_code + ", partner_id=" + partner_id
				+ ", product_uom_id=" + product_uom_id 
				+ "]";
	}
	
	

}
