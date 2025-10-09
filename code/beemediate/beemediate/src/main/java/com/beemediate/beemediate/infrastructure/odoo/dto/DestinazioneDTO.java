package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa informazioni di contatto relative al luogo di consegna. I campi rimappano alcuni attributi richiesti al model <i>res.partner</i> di Odoo.
 */
public class DestinazioneDTO{
	
	/**
	 * Mapping di id.
	 */
	private Optional<Integer> id;
	/**
	 * Mapping di ref.
	 */
	private Optional<String> codiceDestinazione;
	
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
