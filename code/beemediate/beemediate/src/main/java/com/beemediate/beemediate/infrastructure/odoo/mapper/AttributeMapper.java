package com.beemediate.beemediate.infrastructure.odoo.mapper;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.Optional;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Classe utility per fare inferenza sui model fields del XML ricevuto da Odoo.
 */
public final class AttributeMapper {
	
	/**
	 * Logger
	 */
	private static final Logger LOG = LoggerFactory.getLogger(AttributeMapper.class);

	private AttributeMapper() {/*empty constructor*/}
	
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java  String.
	 * @param o - Object
	 * @return Optional contenente String, oppure <i>Optional.empty()</i>;
	 */
	public static Optional<String> stringify(final Object o) {
		return (o instanceof String)? Optional.of((String) o) : Optional.empty();
	}
	
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java  Integer.
	 * @param o - Object
	 * @return Optional contenente Integer, oppure <i>Optional.empty()</i>;
	 */
	public static Optional<Integer> intify(final Object o) {
		return (o instanceof Integer)? Optional.of((Integer) o) : Optional.empty();
	}
	
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java  Object[].
	 * @param o - Object
	 * @return Optional contenente Object[], oppure <i>Optional.empty()</i>;
	 */
	public static Optional<Object[]> toArray(final Object o) {
		return (o instanceof Object[])? Optional.of((Object[]) o) : Optional.empty();
	}
	
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java  Boolean.
	 * @param o - Object
	 * @return Optional contenente Boolean, oppure <i>Optional.empty()</i>;
	 */
    public static Optional<Boolean> booleanify(final Object o) {
    	return (o instanceof Boolean)? Optional.of((Boolean) o) : Optional.empty();
	}
    
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java  Double.
	 * @param o - Object
	 * @return Optional contenente Double, oppure <i>Optional.empty()</i>;
	 */
    public static Optional<Double> doublify(final Object o){
    	return (o instanceof Double)? Optional.of((Double) o) : Optional.empty();
    }
	
	/**
	 * Valuta se l'oggetto in input è compatibile col tipo Java LocalDateTime con formato "yyyy-MM-dd HH:mm:ss".
	 * @param o - Object
	 * @return Optional contenente LocalDateTime, oppure <i>Optional.empty()</i>;
	 */
	public static Optional<LocalDateTime> toLocalDateTime(final Object o) {
		
		final Optional<String> temp = stringify( o );
		if(temp.isEmpty())
			return Optional.empty();
		
		final String s = temp.get();
        final DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        LocalDateTime dateTime = null;
        try {
        	dateTime = LocalDateTime.parse(s, formatter);
        }catch(DateTimeParseException e) {
        	LOG.info(e.getMessage());
        }
		return dateTime==null? Optional.empty() : Optional.of(dateTime);
	}
}
