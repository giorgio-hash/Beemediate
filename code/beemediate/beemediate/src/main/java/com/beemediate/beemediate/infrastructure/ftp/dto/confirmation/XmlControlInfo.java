package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Informazioni di controllo sulla generazione del documento
 */
@JacksonXmlRootElement(localName = "CONTROL_INFO")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlControlInfo {
	
	/**
	 * Informazioni sul creatore della conferma d'ordine
	 */
	@JacksonXmlProperty(localName="GENERATOR_INFO")
	private String generatorInfo;

	/**
	 * data di creazione del file XML
	 */
	@JacksonXmlProperty(localName="GENERATION_DATE")
	private String generationDate;

	/**
	 * 
	 * @return String
	 */
	public String getGeneratorInfo() {
		return generatorInfo;
	}

	/**
	 * 
	 * @param generatorInfo - String
	 */
	public void setGeneratorInfo(String generatorInfo) {
		this.generatorInfo = generatorInfo;
	}

	/**
	 * 
	 * @return String
	 */
	public String getGenerationDate() {
		return generationDate;
	}

	/**
	 * 
	 * @param generationDate - String
	 */
	public void setGenerationDate(String generationDate) {
		this.generationDate = generationDate;
	}

	
	
}
