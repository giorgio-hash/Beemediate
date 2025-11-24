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
 * DTO che mappa informazioni di contatto relative al luogo di consegna. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class DestinazioneDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di ref.
	 */
	private final Optional<String> codiceDestinazione;
	
	
	/**
	 * Static factory method che interagisce col model res.partner di Odoo per estrarre informazioni di contatto relative al luogo di consegna.
	 * @param concons - ContattoConsegnaDTO
	 * @return DestinazioneDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static DestinazioneDTO fromXMLRPC(final OdooApiConfig odoo, final ContattoConsegnaDTO concons) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {

		if (concons == null || concons.getPartnerId().getNum().isEmpty() ) throw new InconsistentDTOException("Oggetto ContattoConsegnaDTO non ha le informazioni necessarie");
		
		final Object id = concons.getPartnerId().getNum().get();
		final Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList("ref"));
		res = odoo.readFromModel(odoo.RES_PARTNER, requestInfo, id);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della destinazione.");
		
		return new DestinazioneDTO( (HashMap<String, Object>) res[0]);
	}
	
	/**
	 * 
	 * @param map - Map contente una tupla del model <i>res.partner</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public DestinazioneDTO( final Map<String, Object> map) {
		id = AttributeMapper.intify( map.get("id") );
		codiceDestinazione = AttributeMapper.stringify( map.get("ref") );
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
	public Optional<String> getCodiceDestinazione() {
		return codiceDestinazione;
	}

	@Override
	public String toString() {
		return "DestinazioneDTO [id=" + id + ", codiceDestinazione=" + codiceDestinazione + "]";
	}

	
}
