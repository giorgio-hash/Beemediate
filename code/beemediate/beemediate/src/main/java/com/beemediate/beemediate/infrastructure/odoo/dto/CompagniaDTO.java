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
 * DTO che mappa i dati della compagnia cliente che gestisce il CRM Odoo. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class CompagniaDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di company_registry.
	 */
	private final Optional<String> companyRegistry;
	
	
	/**
	 * Static factory method che interagisce col model res.partner per estrarre informazioni di contatto della compagnia cliente, secondo il preventivo.
	 * @param odoo - OdooApiConfig
	 * @param prv - PreventivoDTO
	 * @return CompagniaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static CompagniaDTO fromXMLRPC(final OdooApiConfig odoo, final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (prv == null || prv.getCompanyId().getNum().isEmpty() ) throw new InconsistentDTOException("Oggetto PreventivoDTO non ha le informazioni necessarie");
		
		final Object id = prv.getCompanyId().getNum().get();
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList("ref"));
		res = (Object[]) odoo.models.execute(odoo.EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						odoo.RES_PARTNER,odoo.READ,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della compagnia ");
		
		return new CompagniaDTO( (HashMap<String, Object>) res[0]);
	}
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>res.partner</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public CompagniaDTO( final Map<String, Object> map ) {
		id = AttributeMapper.intify( map.get("id") );
		companyRegistry = AttributeMapper.stringify( map.get("ref") ); 
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
	public Optional<String> getCompanyRegistry() {
		return companyRegistry;
	}

	@Override
	public String toString() {
		return "CompagniaDTO [id=" + id + ", company_registry=" + companyRegistry + "]";
	}
	
	
}
