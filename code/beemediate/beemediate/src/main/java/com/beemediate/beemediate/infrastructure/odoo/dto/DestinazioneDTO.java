package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

public class DestinazioneDTO extends XmlDTO{
	
	private Optional<Integer> id;
	private Optional<String> codiceDestinazione;
	
	public DestinazioneDTO( Map<String, Object> map) {
		id = intify( map.get("id") );
		codiceDestinazione = stringify( map.get("ref") );
	}

	public Optional<Integer> getId() {
		return id;
	}

	public Optional<String> getCodiceDestinazione() {
		return codiceDestinazione;
	}

	@Override
	public String toString() {
		return "DestinazioneDTO [id=" + id + ", codiceDestinazione=" + codiceDestinazione + "]";
	}

	
}
