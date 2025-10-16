package com.beemediate.beemediate.infrastructure.ftp.mapper;

import java.util.Arrays;

import org.springframework.beans.factory.annotation.Autowired;

import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlItem;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrder;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrderHeader;
import com.beemediate.beemediate.infrastructure.ftp.dto.XmlOrderSummary;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.dataformat.xml.XmlMapper;

public class DataMapper {

	@Autowired
	private static XmlMapper xmlMapper = new XmlMapper();
	
	
	
	public static String mapToXml(OrderStructure os) {
		
		try {
			return xmlMapper.writeValueAsString(
								new XmlOrder(
										new XmlOrderHeader(os.getHeader()),
										Arrays.stream(os.getItemList())
								          		.map(XmlItem::new)
								          		.toList(),
										new XmlOrderSummary(os.getOrderSummary())												)
										);
		} catch (JsonProcessingException e) {
			e.printStackTrace();
		}
		return null;
	}
	
}
