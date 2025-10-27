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
 * DTO che mappa i dettagli relativi al luogo di consegna. I campi rimappano alcuni attributi richiesti al model <i>stock.warehouse</i> di Odoo.
 */
public class ContattoConsegnaDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di partner_id.
	 */
	private final IdentifierDTO partnerId;
	
	
	/**
	 * Static factory method che interagisce col model stock.warehouse di Odoo per estrarre i dettagli relativi al luogo di consegna.
	 * @param odoo - OdooApiConfig
	 * @param cns - ConsegnaDTO
	 * @return ContattoConsegnaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static ContattoConsegnaDTO fromXMLRPC(final OdooApiConfig odoo, final ConsegnaDTO cns) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (cns == null || cns.getWarehouseId().getNum().isEmpty()) throw new InconsistentDTOException("Oggetto ConsegnaDTO non ha le informazioni necessarie");
		
		final Object id = cns.getWarehouseId().getNum().get();
		final Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList(odoo.PARTNER_ID_FIELD));
		res = (Object[]) odoo.models.execute(odoo.EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.warehouse",odoo.READ,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni del contatto di consegna.");
		
		return new ContattoConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
	/**
	 * 
	 * @param map - Map contente una tupla del model <i>stock.warehouse</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ContattoConsegnaDTO( final Map<String, Object> map ) {
		id = AttributeMapper.intify( map.get("id") );
		partnerId = new IdentifierDTO( (Object[]) map.get("partner_id") );
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
	 * @return oggetto IdentifierDTO con identificativo della compagnia.
	 */
	public IdentifierDTO getPartnerId() {
		return partnerId;
	}

	@Override
	public String toString() {
		return "ContattoConsegnaDTO [id=" + id + ", partner_id=" + partnerId + "]";
	}
	
	
}
