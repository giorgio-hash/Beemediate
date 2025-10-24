package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Proprietà dell'articolo
 */
@JacksonXmlRootElement(localName = "FEATURE")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlProductFeature {
	
	/**
	 * Nome della proprietà dell'articolo
	 */
	@JacksonXmlProperty(localName="bmecat:FNAME")
	private String fname;
	
	/**
	 * Quantità ordinata in pezzi
	 */
	@JacksonXmlProperty(localName="bmecat:FVALUE")
	private float fvalue;
	
	/**
	 * unità ISO "pezzo"
	 */
	@JacksonXmlProperty(localName="bmecat:FUNIT")
	private String funit;

	/**
	 * 
	 * @return String
	 */
	public String getFname() {
		return fname;
	}

	/**
	 * 
	 * @param fname - String
	 */
	public void setFname(String fname) {
		this.fname = fname;
	}

	/**
	 * 
	 * @return String
	 */
	public float getFvalue() {
		return fvalue;
	}

	/**
	 * 
	 * @param fvalue - float
	 */
	public void setFvalue(float fvalue) {
		this.fvalue = fvalue;
	}

	/**
	 * 
	 * @return String
	 */
	public String getFunit() {
		return funit;
	}

	/**
	 * 
	 * @param funit - String
	 */
	public void setFunit(String funit) {
		this.funit = funit;
	}
	
	
}
