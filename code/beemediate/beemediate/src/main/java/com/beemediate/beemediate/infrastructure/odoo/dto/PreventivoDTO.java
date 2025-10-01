package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.time.LocalDateTime;
import java.util.Map;
import java.util.Optional;

public class PreventivoDTO extends XmlDTO{
	
	private Optional<Integer> id;
	private Optional<String> name;
	private FieldIdentifierDTO partner_id;
	private FieldIdentifierDTO product_id;
	private FieldIdentifierDTO currency_id;
	private FieldIdentifierDTO picking_type_id;
	private FieldIdentifierDTO company_id;
	private Optional<String> origin;
	private Optional<Object[]> order_line;
	private Optional<LocalDateTime> date_order;
	private Optional<LocalDateTime> date_approve;
	private Optional<LocalDateTime> date_planned;
//	[{'id': 4,
//		  'name': 'P00004',
//		  'partner_id': [8, 'GEALAN'],
//		  'product_id': [3, 'gamba per sedia'],
//		  'origin': 'OP/00006 - S00005, OP/00007 - S00005, OP/00005 - S00005, OP/00004 '
//		            '- S00005',
//		  'order_line': [10, 11, 12, 13],
//		  'currency_id': [125, 'EUR'],
//		  'date_order': '2025-09-18 12:00:00',
//		  'date_approve': False,
//		  'date_planned': '2025-09-19 12:00:00',
//		  'picking_type_id': [1, 'edu-trySerramenti2: Receipts']]
	
	public PreventivoDTO(Map<String, Object> map) {
		
		id = intify(map.get("id"));
		
		name = stringify(map.get("name"));
		
		partner_id = new FieldIdentifierDTO( (Object[]) map.get("partner_id") );
		
		product_id = new FieldIdentifierDTO( (Object[]) map.get("product_id") );
		
		currency_id = new FieldIdentifierDTO( (Object[]) map.get("currency_id") );
		
		picking_type_id = new FieldIdentifierDTO( (Object[]) map.get("picking_type_id") );
		
		company_id = new FieldIdentifierDTO( (Object[]) map.get("company_id") );
		
		origin = stringify( map.get("origin") );
		
		order_line = toArray( map.get("order_line") );
		
		date_order = toLocalDateTime( map.get("date_order") );
		
		date_approve = toLocalDateTime( map.get("date_approve") );
		
		date_planned = toLocalDateTime( map.get("date_planned") );
	}

	public Optional<Integer> getId() {
		return id;
	}

	public Optional<String> getName() {
		return name;
	}

	public FieldIdentifierDTO getPartner_id() {
		return partner_id;
	}

	public FieldIdentifierDTO getProduct_id() {
		return product_id;
	}

	public FieldIdentifierDTO getCurrency_id() {
		return currency_id;
	}

	public FieldIdentifierDTO getPicking_type_id() {
		return picking_type_id;
	}

	public FieldIdentifierDTO getCompany_id() {
		return company_id;
	}

	public Optional<String> getOrigin() {
		return origin;
	}

	public Optional<Object[]> getOrder_line() {
		return order_line;
	}

	public Optional<LocalDateTime> getDate_order() {
		return date_order;
	}

	public Optional<LocalDateTime> getDate_approve() {
		return date_approve;
	}

	public Optional<LocalDateTime> getDate_planned() {
		return date_planned;
	}

	@Override
	public String toString() {
		return "PreventivoDTO [id=" + id + ", name=" + name + ", partner_id=" + partner_id + ", product_id="
				+ product_id + ", currency_id=" + currency_id + ", picking_type_id=" + picking_type_id + ", company_id="
				+ company_id + ", origin=" + origin + ", order_line=" + order_line + ", date_order=" + date_order
				+ ", date_approve=" + date_approve + ", date_planned=" + date_planned 
				+  "]";
	}
	
	
	
}
