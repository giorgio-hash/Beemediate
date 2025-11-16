package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

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
 * Test mapping specifico per Confirmation.xml usando ResourceLoader.
 */
public class ConfirmationXmlTest {

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
    public void deserializeOrderResponseInfoAndValidateFields() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/confirmation/Confirmation.xml");
        assertTrue("resource must exist in classpath: xml/confirmation/Confirmation.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);
            JsonNode header = root.path("ORDERRESPONSE_HEADER");
            assertFalse("ORDERRESPONSE_HEADER must exist", header.isMissingNode());
            JsonNode infoNode = header.path("ORDERRESPONSE_INFO");
            assertFalse("ORDERRESPONSE_INFO must exist", infoNode.isMissingNode());

            XmlOrderResponseInfo info = mapper.treeToValue(infoNode, XmlOrderResponseInfo.class);
            assertNotNull("deserialized XmlOrderResponseInfo", info);

            // campi controllati nell'esempio
            assertEquals("730940155", info.getSupplierOrderId());
            assertEquals("EUR", info.getCurrency());
            assertNotNull("remarks should be present", info.getRemarks());
        }
    }
}