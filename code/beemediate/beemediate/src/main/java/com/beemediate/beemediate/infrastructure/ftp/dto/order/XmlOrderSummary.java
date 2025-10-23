package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.domain.pojo.order.OrderSummary;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlProperty;
import com.fasterxml.jackson.dataformat.xml.annotation.JacksonXmlRootElement;

/**
 *  Mappatura XML-OpenTrans con sintesi dell'ordine. Può essere istanziata con il POJO {@code OrderItem}
 */
@JacksonXmlRootElement(localName = "ORDER_SUMMARY")
public class XmlOrderSummary {
	
	/**
	 * tag con numero di articoli dell'ordine
	 */
	@JacksonXmlProperty(localName="TOTAL_ITEM_NUM")
	private final int totalItemNum;
	
	/**
	 * Costruttore per creare struttura XML-OpenTrans sintesi dell'ordine partendo dal POJO {@code OrderSummary}
	 * @param summary - OrderSummary
	 */
	public XmlOrderSummary(final OrderSummary summary) {
		this.totalItemNum = summary.getTotalItemNum();
	}
	
	/**
	 * 
	 * @return int
	 */
	public int getTotalItemNum() {
		return totalItemNum;
	}
	
	
}
