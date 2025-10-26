package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 * Mappatura XML-OpenTrans per header ordine, contenente informazioni sulla transazione. Può prendere in input il POJO {@code OrderHeader}
 */
@JacksonXmlRootElement(localName = "ORDER_HEADER")
public class XmlOrderHeader {
	
	/**
	 * Riferimento a DTO XmlOrderInfo per ORDER_INFO.
	 */
	@JacksonXmlProperty(localName="ORDER_INFO")
	private final XmlOrderInfo orderInfo;

	/**
	 * Rifeirmento a DTO XmlAgreement per AGREEMENT
	 */
	@JacksonXmlProperty(localName="AGREEMENT")
	private XmlAgreement agreement;
	
	/**
	 * Ordini di contratto
	 */
	public class XmlAgreement {
		/**
		 * Numero di contratto
		 */
		@JacksonXmlProperty(localName="bmecat:AGREEMENT_ID")
		@JsonInclude(JsonInclude.Include.ALWAYS)
		private String id;

		/**
		 * Costruttore
		 * @param id
		 */
		public XmlAgreement(String id) {
			this.id=id;
		}
		/**
		 * 
		 * @return
		 */
		public String getId() {
			return id;
		}

		/**
		 * 
		 * @param id
		 */
		public void setId(String id) {
			this.id = id;
		}	
	}
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans header ordine partendo dal POJO {@code OrderHeader}
	 * @param head - OrderHeader
	 */
	public XmlOrderHeader(final OrderHeader head) {
		super();
		this.orderInfo = new XmlOrderInfo( head );
		this.agreement = new XmlAgreement(null);
	}

	/**
	 * 
	 * @return XmlOrderInfo
	 */
	public XmlOrderInfo getOrderInfo() {
		return orderInfo;
	}

	
}
