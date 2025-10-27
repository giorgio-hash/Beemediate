package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;
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
	 * Static factory method che interagisce col model stock.picking.type di Odoo per estrarre il luogo di consegna definito nel preventivo.
	 * @param odoo - OdooApiConfig
	 * @param prv - PreventivoDTO
	 * @return ConsegnaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static ConsegnaDTO fromXMLRPC(final OdooApiConfig odoo, final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (prv == null || prv.getPickingTypeId().getNum().isEmpty()) throw new InconsistentDTOException("Oggetto PreventivoDTO non ha le informazioni necessarie");
		
		final Object id = prv.getPickingTypeId().getNum().get();
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList("warehouse_id"));
		res = (Object[]) odoo.models.execute(odoo.EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.picking.type",odoo.READ,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni sulla consegna.");
		
		return new ConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
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
