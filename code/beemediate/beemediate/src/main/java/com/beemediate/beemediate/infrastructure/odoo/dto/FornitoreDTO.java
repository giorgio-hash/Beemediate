package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa informazioni di contatto fornitore. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class FornitoreDTO{
	
	/**
	 * Mapping di name
	 */
	private final Optional<String> name;
	/**
	 * Mapping di ref
	 */
	private final Optional<String> codiceAzienda;
	/**
	 * Mapping di id
	 */
	private final Optional<Integer> id;
	
	
	/**
	 * Static factory method che interagisce col model res.partner di Odoo per recuperare le informazioni di contatto fornitore.
	 * @return FornitoreDTO
	 * @throws EmptyFetchException
	 * @throws XmlRpcException
	 */
	public static FornitoreDTO fromXMLRPC(final OdooApiConfig odoo) throws EmptyFetchException, XmlRpcException {
		Object[] ids;
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		//cerca GEALAN
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute(odoo.EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						odoo.RES_PARTNER,"search",
						Arrays.asList(Arrays.asList(Arrays.asList("name","=","GEALAN"))),
						requestInfo
						)
				);
		
		if(ids.length == 0) throw new EmptyFetchException ("Non trovo GEALAN");
		
		//estrai GEALAN
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList("name","ref"));
		res = (Object[]) odoo.models.execute(odoo.EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						odoo.RES_PARTNER,odoo.READ,
						Arrays.asList(ids),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato GEALAN, ma non riesco ad estrarlo.");
		
		
		return new FornitoreDTO( (HashMap<String, Object>) res[0] );
	}
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>res.partner</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public FornitoreDTO(final Map<String, Object> map) {
		name = AttributeMapper.stringify(map.get("name"));
		codiceAzienda = AttributeMapper.stringify(map.get("ref"));
		id = AttributeMapper.intify(map.get("id"));
	}
	
	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getName() {
		return name;
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
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String>  getCodiceAzienda() {
		return codiceAzienda;
	}
	
	@Override
	public String toString() {
		return "FornitoreDTO [name=" + name + ", codiceAzienda=" + codiceAzienda + ", id=" + id
				+ "]";
	}
	
	

}
