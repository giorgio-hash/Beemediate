package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.beemediate.beemediate.infrastructure.ftp.dto.confirmation.XmlOrderResponseInfo;
import com.ctc.wstx.stax.WstxInputFactory;
import com.ctc.wstx.stax.WstxOutputFactory;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.dataformat.xml.XmlFactory;
import com.fasterxml.jackson.dataformat.xml.XmlMapper;
import org.junit.Before;
import org.junit.Test;
import org.springframework.core.io.DefaultResourceLoader;
import org.springframework.core.io.Resource;
import org.springframework.core.io.ResourceLoader;

import java.io.InputStream;

import javax.xml.stream.XMLInputFactory;

import static org.junit.Assert.*;

/**
 * Test sulla struttura dell'ORDER di esempio (ESEMPIO_CASO_REALE.xml) usando ResourceLoader.
 */
public class OrderXmlStructureTest {

    private XmlMapper mapper;
    private ResourceLoader resourceLoader;

    private XmlMapper getXmlMapper() {
		// disattiva la risoluzione del namespace: 
		// https://github.com/FasterXML/jackson-dataformat-xml/issues/63
		XMLInputFactory f = new WstxInputFactory();
		f.setProperty(XMLInputFactory.IS_NAMESPACE_AWARE, Boolean.FALSE);
		XmlMapper m = new XmlMapper(new XmlFactory(f, new WstxOutputFactory()));
        // non far fallire su campi ignoti: le classi DTO hanno @JsonIgnoreProperties(ignoreUnknown=true)
        m.configure(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES, false);
        m.configure(DeserializationFeature.ACCEPT_SINGLE_VALUE_AS_ARRAY, true);
        return m;
    }

    @Before
    public void setUp() {
        mapper = getXmlMapper();
        resourceLoader = new DefaultResourceLoader();
    }

    @Test
    public void parseOrderAndCheckSummaryTotalItems() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);
            JsonNode summaryNode = root.path("ORDER_SUMMARY");
            assertFalse("ORDER_SUMMARY must exist", summaryNode.isMissingNode());
            XmlOrderSummary summary = mapper.treeToValue(summaryNode, XmlOrderSummary.class);
            assertNotNull("deserialized XmlOrderSummary", summary);
            assertEquals(8, summary.getTotalItemNum());

            JsonNode itemList = root.path("ORDER_ITEM_LIST");
            assertFalse("ORDER_ITEM_LIST must exist", itemList.isMissingNode());
            JsonNode itemsNodeList = itemList.path("ORDER_ITEM");
            assertFalse("ORDER_ITEM should exist", itemsNodeList.isMissingNode());
            if (itemsNodeList.isArray()) {
                assertEquals(8, itemsNodeList.size());
                XmlItem item = null;
                for(JsonNode itemNode : itemsNodeList) {
                	item = mapper.treeToValue(itemNode, XmlItem.class);
                	assertNotNull("deserialized XmlItem", item);
                }
            } else {
                // fallback: se non è array, almeno 1 elemento
                int count = 0;
                for (JsonNode ignored : itemList) count++;
                assertTrue("should have at least 1 ORDER_ITEM", count >= 1);
                XmlItem item = null;
                item = mapper.treeToValue(itemsNodeList, XmlItem.class);
                assertNotNull("deserialized XmlItem", item);
            }
        }
    }
    
    @Test
    public void parseOrderAndCheckHeader() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);

            JsonNode headerNode = root.path("ORDER_HEADER");
            assertFalse("ORDER_HEADER must exist", headerNode.isMissingNode());
            XmlOrderHeader header = mapper.treeToValue(headerNode, XmlOrderHeader.class);
            assertNotNull("deserialized XmlOrderHeader", header);

            JsonNode infoNode = headerNode.path("ORDER_INFO");
            assertFalse("ORDER_INFO must exist", infoNode.isMissingNode());
            XmlOrderInfo info = mapper.treeToValue(infoNode, XmlOrderInfo.class);
            assertNotNull("deserialized XmlOrderInfo", info);

            JsonNode orderId = infoNode.path("ORDER_ID");
            assertFalse("ORDER_ID must exist", orderId.isMissingNode());
            assertEquals("ORDER_ID correctly mapped", info.getOrderId(), orderId.asText().trim());

            JsonNode orderDate = infoNode.path("ORDER_DATE");
            assertFalse("ORDER_DATE must exist", orderDate.isMissingNode());
            assertEquals("ORDER_DATE correctly mapped", info.getOrderDate() , orderDate.asText().trim());

            JsonNode currency = infoNode.path("bmecat:CURRENCY");
            assertFalse("bmecat:CURRENCY must exist under ORDER_INFO", currency.isMissingNode());
            assertEquals("bmecat:CURRENCY correctly mapped", info.getCurrency(), currency.asText().trim());

            // verify parties exist and at least one PARTY is present
            JsonNode parties = infoNode.path("PARTIES");
            assertFalse("PARTIES must exist", parties.isMissingNode());
            JsonNode partyNodeList = parties.path("PARTY");
            assertFalse("PARTIES not empty", partyNodeList.isMissingNode());
            assertTrue("PARTIES is an array", partyNodeList.isArray());
            XmlParty party = null;
            for(JsonNode node : partyNodeList) {
            	party = mapper.treeToValue(node, XmlParty.class);
            	assertNotNull("deserialized XmlParty", node);
            }
        }
    }

    @Test
    public void ParseOrderAndCheckAttributes() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode original = mapper.readTree(is);
            // map genericamente in un oggetto Java (LinkedHashMap / Lists)
            XmlOrder dto = mapper.treeToValue(original, XmlOrder.class);
            assertNotNull("DTO after treeToValue should not be null", dto);
            // guardo gli attributi di schema
            assertEquals("XmlOrder has mapped xmlns", original.path("xmlns").toString().replaceAll("\"", ""), dto.getXmlns());
            assertEquals("XmlOrder has mapped xsi", original.path("xmlns:xsi").toString().replaceAll("\"", ""), dto.getXsi());
            assertEquals("XmlOrder has mapped bmecat", original.path("xmlns:bmecat").toString().replaceAll("\"", ""), dto.getBmecat());
            assertEquals("XmlOrder has mapped version", original.path("version").toString().replaceAll("\"", ""), dto.getVersion());
            assertEquals("XmlOrder has mapped type", original.path("type").toString().replaceAll("\"", ""), dto.getType());
            assertEquals("XmlOrder has mapped schema_location", original.path("xsi:schemaLocation").toString().replaceAll("\"", ""), dto.getSchemaLocation());

            // serializza di nuovo in JsonNode e confronta strutturalmente
            //JsonNode reserialized = mapper.valueToTree(dto);
            //assertNotNull("reserialized JsonNode should not be null", reserialized);

            //assertEquals("Round-trip structural equality for ORDER", original, reserialized);
        }
    }
}