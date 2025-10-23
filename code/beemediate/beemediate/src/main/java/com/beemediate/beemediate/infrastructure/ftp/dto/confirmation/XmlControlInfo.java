package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

@JacksonXmlRootElement(localName = "CONTROL_INFO")
@JsonInclude(JsonInclude.Include.NON_NULL)
@JsonIgnoreProperties(ignoreUnknown = true)
public class XmlControlInfo {
	
	@JacksonXmlProperty(localName="GENERATOR_INFO")
	private String generatorInfo;

	@JacksonXmlProperty(localName="GENERATION_DATE")
	private String generationDate;

	public String getGeneratorInfo() {
		return generatorInfo;
	}

	public void setGeneratorInfo(String generatorInfo) {
		this.generatorInfo = generatorInfo;
	}

	public String getGenerationDate() {
		return generationDate;
	}

	public void setGenerationDate(String generationDate) {
		this.generationDate = generationDate;
	}

	
	
}
