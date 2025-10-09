package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dati del luogo di consegna definito nel preventivo. I campi rimappano alcuni attributi richiesti al model <i>stock.picking.type</i> di Odoo.
 */
public class ConsegnaDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di warehouse_id.
	 */
	private final IdentifierDTO warehouseId;
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>stock.picking.type</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ConsegnaDTO ( final Map<String, Object> map ) {
		
		id = AttributeMapper.intify( map.get("id") );
		
		warehouseId = new IdentifierDTO( (Object[]) map.get("warehouse_id") );
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
	 * @return oggetto IdentifierDTO con identificativo del magazzino o luogo.
	 */
	public IdentifierDTO getWarehouseId() {
		return warehouseId;
	}
	
	@Override
	public String toString() {
		return "ConsegnaDTO [id=" + id + ", warehouse_id=" + warehouseId + "]";
	}	

}
