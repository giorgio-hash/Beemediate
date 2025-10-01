package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.Optional;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


abstract class XmlDTO {
	
	private final Logger log = LoggerFactory.getLogger(XmlDTO.class);

	protected Optional<String> stringify(Object o) {
		return (o instanceof String)? Optional.of((String) o) : Optional.empty();
	}
	
	protected Optional<Integer> intify(Object o) {
		return (o instanceof Integer)? Optional.of((Integer) o) : Optional.empty();
	}
	
	protected Optional<Object[]> toArray(Object o) {
		return (o instanceof Object[])? Optional.of((Object[]) o) : Optional.empty();
	}
	
    protected Optional<Boolean> booleanify(Object o) {
    	return (o instanceof Boolean)? Optional.of((Boolean) o) : Optional.empty();
	}
    
    protected Optional<Double> doublify(Object o){
    	return (o instanceof Double)? Optional.of((Double) o) : Optional.empty();
    }
	
	protected Optional<LocalDateTime> toLocalDateTime(Object o) {
		
		Optional<String> temp = stringify( o );
		if(temp.isEmpty())
			return Optional.empty();
		
		String s = temp.get();
        DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        LocalDateTime dateTime = null;
        try {
        	dateTime = LocalDateTime.parse(s, formatter);
        }catch(DateTimeParseException e) {
        	log.info(e.getMessage());
        }
		return dateTime==null? Optional.empty() : Optional.of(dateTime);
	}
}
