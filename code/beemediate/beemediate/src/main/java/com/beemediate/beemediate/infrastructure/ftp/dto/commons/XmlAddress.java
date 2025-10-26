package com.beemediate.beemediate.infrastructure.ftp.dto.commons;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * tag per i dettagli di domicilio
 */
@JacksonXmlRootElement(localName="ADDRESS")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlAddress {
	
	/**
	 * nome del luogo di domicilio
	 */
	@JacksonXmlProperty(localName="bmecat:NAME")
	private String name;
	/**
	 * nome della strada di domicilio e numero civico
	 */
	@JacksonXmlProperty(localName="bmecat:STREET")
	private String street;
	/**
	 * codice postale
	 */
	@JacksonXmlProperty(localName="bmecat:ZIP")
	private String zip;
	/**
	 * città
	 */
	@JacksonXmlProperty(localName="bmecat:CITY")
	private String city;
	/**
	 * paese
	 */
	@JacksonXmlProperty(localName="bmecat:COUNTRY")
	private String country;
	/**
	 * paese nel codice ISO 3166-1
	 */
	@JacksonXmlProperty(localName="bmecat:COUNTRY_CODED")
	private String countryCoded;
	/**
	 * nome del luogo di domicilio
	 */
	@JacksonXmlProperty(localName="bmecat:NAME3")
	@JsonInclude(JsonInclude.Include.NON_EMPTY)
	private String name3;
	
	/**
	 * empty constructor for Jackson deserializer
	 */
	public XmlAddress() {/*empty constructor for Jackson deserializer*/}
	
	/**
	 * Costruttore
	 * @param name - String
	 * @param street - String
	 * @param zip - String
	 * @param city - String
	 * @param country - String
	 * @param countryCoded - String
	 */
	public XmlAddress(String name, String street, String zip, String city, String country, String countryCoded) {
		super();
		this.name = name;
		this.street = street;
		this.zip = zip;
		this.city = city;
		this.country = country;
		this.countryCoded = countryCoded;
	}


	/**
	 * 
	 * @return String
	 */
	public String getName() {
		return name;
	}

	/**
	 * 
	 * @return String
	 */
	public String getStreet() {
		return street;
	}

	/**
	 * 
	 * @return String
	 */
	public String getZip() {
		return zip;
	}

	/**
	 * 
	 * @return String
	 */
	public String getCity() {
		return city;
	}

	/**
	 * 
	 * @return String
	 */
	public String getCountry() {
		return country;
	}

	/**
	 * 
	 * @return String
	 */
	public String getCountryCoded() {
		return countryCoded;
	}
	
	

}
