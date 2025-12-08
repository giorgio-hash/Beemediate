package com.beemediate.beemediate.infrastructure.ftp.dto.confirmation;

import com.beemediate.beemediate.domain.pojo.confirmation.ConfirmationStructure;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlAddress;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlOrderPartiesReference;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlPartyID;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlProductID;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;
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

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

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
    public void deserializeOrderResponseAndValidateFields() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/confirmation/Confirmation.xml");
        assertTrue("resource must exist in classpath: xml/confirmation/Confirmation.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            
        	//RADICE
        	JsonNode root = mapper.readTree(is);
        	XmlOrderResponse xo = DataMapper.deserializeXmlOrderResponse(res.getContentAsString( StandardCharsets.UTF_8));
        	assertEquals(root.path("xmlns").toString().replaceAll("\"", ""), xo.getXmlns());
        	assertEquals(root.path("xmlns:xsi").toString().replaceAll("\"", ""), xo.getXsi());
        	assertEquals(root.path("xmlns:bmecat").toString().replaceAll("\"", ""), xo.getBmecat());
        	assertEquals(root.path("version").toString().replaceAll("\"", ""), xo.getVersion());
        	
        	//HEADER
        	JsonNode headerNode = root.path("ORDERRESPONSE_HEADER");
        	XmlOrderResponseHeader xh = xo.getOrderResponseHeader();
        	
        	JsonNode controlInfoNode = headerNode.path("CONTROL_INFO");
        	XmlControlInfo xci = xh.getControlInfo();
        	assertEquals(controlInfoNode.path("GENERATOR_INFO").toString().replaceAll("\"", ""), xci.getGeneratorInfo());
        	assertEquals(controlInfoNode.path("GENERATION_DATE").toString().replaceAll("\"", ""), xci.getGenerationDate());
        	
        	JsonNode infoNode = headerNode.path("ORDERRESPONSE_INFO");
        	XmlOrderResponseInfo xori = xh.getOrderResponseInfo();
        	assertEquals(infoNode.path("ORDER_ID").toString().replaceAll("\"", ""), xori.getOrderId());
        	assertEquals(infoNode.path("ORDERRESPONSE_DATE").toString().replaceAll("\"", ""), xori.getOrderResponseDate());
        	assertEquals(infoNode.path("ORDER_DATE").toString().replaceAll("\"", ""), xori.getOrderDate());
        	assertEquals(infoNode.path("ALT_CUSTOMER_ORDER_ID").toString().replaceAll("\"", ""), xori.getAltCustomerOrderId());
        	assertEquals(infoNode.path("SUPPLIER_ORDER_ID").toString().replaceAll("\"", ""), xori.getSupplierOrderId());
        	JsonNode remarksNode = infoNode.path("REMARKS");
        	XmlRemarks xr = xori.getRemarks();
        	assertEquals(remarksNode.path("").toString().replaceAll("\"", ""), xr.getRemarks());
        	assertEquals(remarksNode.path("type").toString().replaceAll("\"", ""), xr.getType());
        	assertEquals(infoNode.path("bmecat:CURRENCY").toString().replaceAll("\"", ""), xori.getCurrency());
        	
        	JsonNode deliveryDateNode = infoNode.path("DELIVERY_DATE");
        	XmlDeliveryDate xdd = xori.getDeliveryDate();
        	assertEquals(deliveryDateNode.path("type").toString().replaceAll("\"", ""), xdd.getType());
        	assertEquals(deliveryDateNode.path("DELIVERY_START_DATE").toString().replaceAll("\"", ""), xdd.getDeliveryStartDate());
        	assertEquals(deliveryDateNode.path("DELIVERY_END_DATE").toString().replaceAll("\"", ""), xdd.getDeliveryEndDate());
            
        	JsonNode parties = infoNode.path("PARTIES");// verify parties exist and at least one PARTY is present
            assertFalse("PARTIES must exist", parties.isMissingNode());
            JsonNode partyNode = parties.path("PARTY");
            XmlParty xp = xori.getParties().get(0);
            XmlPartyID xpid =  xp.getPartyId();
            assertEquals(partyNode.path("bmecat:PARTY_ID").path("").toString().replaceAll("\"", ""), xpid.getPartyId());
            assertEquals(partyNode.path("bmecat:PARTY_ID").path("type").toString().replaceAll("\"", ""), xpid.getType());
            assertEquals(partyNode.path("PARTY_ROLE").toString().replaceAll("\"", ""), xp.getPartyRole());
        	JsonNode addressNode = partyNode.path("ADDRESS");
            XmlAddress xa = xp.getAddress();
            assertEquals(addressNode.path("bmecat:NAME").toString().replaceAll("\"", ""), xa.getName());
            assertEquals(addressNode.path("bmecat:STREET").toString().replaceAll("\"", ""), xa.getStreet());
            assertEquals(addressNode.path("bmecat:ZIP").toString().replaceAll("\"", ""), xa.getZip());
            assertEquals(addressNode.path("bmecat:CITY").toString().replaceAll("\"", ""), xa.getCity());
            assertEquals(addressNode.path("bmecat:COUNTRY").toString().replaceAll("\"", ""), xa.getCountry());
            assertEquals(addressNode.path("bmecat:COUNTRY_CODED").toString().replaceAll("\"", ""), xa.getCountryCoded());
            
            JsonNode orderPartiesReferenceNode = infoNode.path("ORDER_PARTIES_REFERENCE");
            XmlOrderPartiesReference xopr = xori.getOrderPartiesReference();
            XmlPartyID xbir = xopr.getBuyerIdRef();
            XmlPartyID xsir = xopr.getSupplierIdRef();
            assertEquals(orderPartiesReferenceNode.path("bmecat:BUYER_IDREF").path("").toString().replaceAll("\"", ""), xbir.getPartyId());
            assertEquals(orderPartiesReferenceNode.path("bmecat:BUYER_IDREF").path("type").toString().replaceAll("\"", ""), xbir.getType());
            assertEquals(orderPartiesReferenceNode.path("bmecat:SUPPLIER_IDREF").path("").toString().replaceAll("\"", ""), xsir.getPartyId());
            assertEquals(orderPartiesReferenceNode.path("bmecat:SUPPLIER_IDREF").path("type").toString().replaceAll("\"", ""), xsir.getType());
            
            
            
            
            
        	//ITEM preso da ITEMLIST
            JsonNode itemNode = root.path("ORDERRESPONSE_ITEM_LIST").path("ORDERRESPONSE_ITEM");
            XmlOrderResponseItem xorItem = xo.getOrderResponseItemList().get(0);
            assertEquals(itemNode.path("LINE_ITEM_ID").toString().replaceAll("\"", ""), String.valueOf(xorItem.getLineItemId()));
            assertEquals(itemNode.path("QUANTITY").toString().replaceAll("\"", "").substring(0, 3), String.valueOf(xorItem.getQuantity()));
            assertEquals(itemNode.path("bmecat:ORDER_UNIT").toString().replaceAll("\"", ""), xorItem.getOrderUnit());
            JsonNode productIdNode = itemNode.path("PRODUCT_ID");
            XmlProductID xpidItem = xorItem.getProductId();
            assertEquals(productIdNode.path("bmecat:SUPPLIER_PID").path("").toString().replaceAll("\"", ""), xpidItem.getSupplierId().getPartyId());
            assertEquals(productIdNode.path("bmecat:SUPPLIER_PID").path("type").toString().replaceAll("\"", ""), xpidItem.getSupplierId().getType());
            assertEquals(productIdNode.path("bmecat:BUYER_PID").path("").toString().replaceAll("\"", ""), xpidItem.getBuyerId().getPartyId());
            assertEquals(productIdNode.path("bmecat:BUYER_PID").path("type").toString().replaceAll("\"", ""), xpidItem.getBuyerId().getType());
            assertEquals(productIdNode.path("bmecat:DESCRIPTION_SHORT").toString().replaceAll("\"", ""), xpidItem.getDescriptionShort());
            JsonNode productFeaturesNode = itemNode.path("PRODUCT_FEATURES");
            JsonNode featureNode = productFeaturesNode.path("FEATURE");
            if (featureNode.isArray()) {
                featureNode = featureNode.get(0);
            }
            XmlProductFeature xpf = xorItem.getProductFeatures().get(0);
            assertEquals(featureNode.path("bmecat:FNAME").toString().replaceAll("\"", ""), xpf.getFname());
            assertEquals(featureNode.path("bmecat:FUNIT").toString().replaceAll("\"", ""), xpf.getFunit());
            assertEquals(featureNode.path("bmecat:FVALUE").toString().replaceAll("\"", "").substring(0, 3), String.valueOf(xpf.getFvalue()));
            JsonNode productPriceFixNode = itemNode.path("PRODUCT_PRICE_FIX");
            XmlProductPriceFix ppf = xorItem.getProductPriceFix();
            assertEquals(productPriceFixNode.path("bmecat:PRICE_AMOUNT").toString().replaceAll("\"", ""), String.valueOf(ppf.getPriceAmount()));
            assertEquals(productPriceFixNode.path("bmecat:PRICE_QUANTITY").toString().replaceAll("\"", ""), String.valueOf(ppf.getPriceQuantity()));
            JsonNode taxDetailsFix = productPriceFixNode.path("TAX_DETAILS_FIX");
            XmlTaxDetailsFix xtdf = ppf.getTaxDetailsFix();
            assertEquals(taxDetailsFix.path("bmecat:TAX").toString().replaceAll("\"", ""), String.valueOf(xtdf.getTax()));
            assertEquals(taxDetailsFix.path("TAX_AMOUNT").toString().replaceAll("\"", ""), String.valueOf(xtdf.getTaxAmount()));
            JsonNode priceBaseFix = productPriceFixNode.path("PRICE_BASE_FIX");
            XmlPriceBaseFix zpbf = ppf.getPriceBaseFix();
            assertEquals(priceBaseFix.path("PRICE_UNIT_VALUE").toString().replaceAll("\"", "").substring(0, 3), String.valueOf(zpbf.getPrice()));
            assertEquals(priceBaseFix.path("bmecat:PRICE_UNIT").toString().replaceAll("\"", ""), String.valueOf(zpbf.getPriceUnit()));
            
            JsonNode deliveryDateItemNode = itemNode.path("DELIVERY_DATE");
            XmlDeliveryDate xddItem = xorItem.getDeliveryDate();
            assertEquals(deliveryDateNode.path("DELIVERY_START_DATE").toString().replaceAll("\"", ""), xddItem.getDeliveryStartDate());
            assertEquals(deliveryDateNode.path("DELIVERY_END_DATE").toString().replaceAll("\"", ""), xddItem.getDeliveryEndDate());
            
            JsonNode remarksItemNode = itemNode.path("REMARKS");
            XmlRemarks xrItem = xorItem.getRemarks();
            assertEquals(remarksItemNode.path("").toString().replaceAll("\"", ""), xrItem.getRemarks());
            assertEquals(remarksItemNode.path("type").toString().replaceAll("\"", ""), xrItem.getType());
            
            
            
            
            
        	//SOMMARIO
            JsonNode summaryNode = root.path("ORDERRESPONSE_SUMMARY");
        	XmlOrderResponseSummary xors = xo.getOrderSummary();
        	assertEquals(summaryNode.path("TOTAL_ITEM_NUM").toString().replaceAll("\"", ""), String.valueOf(xors.getTotalItemNum()));
        	assertEquals(summaryNode.path("TOTAL_AMOUNT").toString().replaceAll("\"", "").substring(0, 5), String.valueOf(xors.getTotalAmount()));
        	JsonNode allowOrChargesFixNode = summaryNode.path("ALLOW_OR_CHARGES_FIX");
            JsonNode allowOrChargeNode = allowOrChargesFixNode.path("ALLOW_OR_CHARGE");
            if (allowOrChargeNode.isArray()) {
            	allowOrChargeNode = allowOrChargeNode.get(0);
            }
            XmlAllowOrCharge xaoc = xors.getAllowOrChargesFix().get(0);
            assertEquals(allowOrChargeNode.path("type").toString().replaceAll("\"", ""), xaoc.gettype());
            assertEquals(allowOrChargeNode.path("ALLOW_OR_CHARGE_NAME").toString().replaceAll("\"", ""), xaoc.getName());
            assertEquals(allowOrChargeNode.path("ALLOW_OR_CHARGE_DESCR").toString().replaceAll("\"", ""), xaoc.getDescr());
            XmlAOCValue xaocv = xaoc.getValue(); 
            assertEquals(allowOrChargeNode.path("ALLOW_OR_CHARGE_VALUE").path("AOC_MONETARY_AMOUNT").toString().replaceAll("\"", "").substring(0, 5), String.valueOf(xaocv.getAmount()));
        }
    }
    
    
    @Test
    public void deserializeAndConvertToPOJO_validateFields() throws IOException {
    	
        Resource res = resourceLoader.getResource("classpath:xml/confirmation/Confirmation.xml");
        assertTrue("resource must exist in classpath: xml/confirmation/Confirmation.xml", res.exists());   	
    	XmlOrderResponse xo = DataMapper.deserializeXmlOrderResponse(res.getContentAsString( StandardCharsets.UTF_8));
 
    	try (InputStream is = res.getInputStream()) {

    		ConfirmationStructure actual = DataMapper.mapConfirmationFromXml(xo);

    		
    		JsonNode root = mapper.readTree(is);
    		JsonNode headerNode = root.path("ORDERRESPONSE_HEADER");
    		JsonNode infoNode = headerNode.path("ORDERRESPONSE_INFO");
    		JsonNode parties = infoNode.path("PARTIES");
    		JsonNode partyNode = parties.path("PARTY");
        	JsonNode addressNode = partyNode.path("ADDRESS");
        	JsonNode deliveryDateNode = infoNode.path("DELIVERY_DATE");
        	JsonNode summaryNode = root.path("ORDERRESPONSE_SUMMARY");
    		
	    	assertEquals(actual.getAddressCity(), addressNode.path("bmecat:CITY").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getAddressCountry(), addressNode.path("bmecat:COUNTRY").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getAddressCountryCoded(), addressNode.path("bmecat:COUNTRY_CODED").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getAddressName(), addressNode.path("bmecat:NAME").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getAddressStreet(), addressNode.path("bmecat:STREET").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getAddressZip(), addressNode.path("bmecat:ZIP").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getCurrency(), infoNode.path("bmecat:CURRENCY").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getDeliveryDate(), deliveryDateNode.path("DELIVERY_START_DATE").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getOrderId(), infoNode.path("ORDER_ID").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getOrderIdGealan(), infoNode.path("SUPPLIER_ORDER_ID").toString().replaceAll("\"", "") );
	    	assertEquals(actual.getOrderResponseDate(), infoNode.path("ORDERRESPONSE_DATE").toString().replaceAll("\"", "") );
	    	assertEquals(String.valueOf(actual.getTotalAmount()), summaryNode.path("TOTAL_AMOUNT").toString().replaceAll("\"", "").substring(0, 5) );
	    	assertEquals(String.valueOf(actual.getTotalItemNum()), summaryNode.path("TOTAL_ITEM_NUM").toString().replaceAll("\"", "") );
	    	
    	}
    }
    
}