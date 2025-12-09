package com.beemediate.beemediate.infrastructure.ftp.dto.order;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import javax.xml.stream.XMLInputFactory;

import org.junit.Before;
import org.junit.Test;
import org.springframework.core.io.DefaultResourceLoader;
import org.springframework.core.io.Resource;
import org.springframework.core.io.ResourceLoader;

import com.beemediate.beemediate.domain.pojo.order.OrderHeader;
import com.beemediate.beemediate.domain.pojo.order.OrderItem;
import com.beemediate.beemediate.domain.pojo.order.OrderStructure;
import com.beemediate.beemediate.domain.pojo.order.OrderSummary;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlDeliveryDate;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlOrderPartiesReference;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlParty;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlProductID;
import com.beemediate.beemediate.infrastructure.ftp.dto.commons.XmlShipmentPartiesReference;
import com.beemediate.beemediate.infrastructure.ftp.mapper.DataMapper;
import com.ctc.wstx.stax.WstxInputFactory;
import com.ctc.wstx.stax.WstxOutputFactory;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.dataformat.xml.XmlFactory;
import com.fasterxml.jackson.dataformat.xml.XmlMapper;

/**
 * Test sulla struttura dell'ORDER di esempio (ESEMPIO_CASO_REALE.xml) usando ResourceLoader, xmlMapper e DataMapper.
 * Test suite per la validazione della struttura e del mapping dei file ORDER (BMEcat).
 * <p>
 * Questa classe utilizza un file reale di esempio ({@code ESEMPIO_CASO_REALE.xml}) per verificare:
 * <ul>
 * <li>La corretta deserializzazione dei campi XML nei DTO infrastrutturali.</li>
 * <li>La consistenza dei dati durante il round-trip di conversione (XML -> DTO -> POJO -> XML).</li>
 * </ul>
 */
public class OrderXmlTest {

    /** Mapper Jackson configurato per la gestione specifica dell'XML BMEcat. */
    private XmlMapper mapper;
    /** Loader per accedere alle risorse nel classpath (es. il file XML di test). */
    private ResourceLoader resourceLoader;

    /**
     * Fabbrica e configura l'istanza di {@link XmlMapper}.
     * <p>
     * Configurazioni chiave:
     * <ul>
     * <li>Disabilitazione del supporto namespace (tramite Woodstox) per semplificare il parsing.</li>
     * <li>Tolleranza verso proprietà sconosciute nel JSON/XML.</li>
     * <li>Accettazione di valori singoli come array per gestire liste con un solo elemento.</li>
     * </ul>
     *
     * @return L'istanza configurata di XmlMapper.
     */
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

    /**
     * Inizializza il mapper e il resource loader prima di ogni test.
     */
    @Before
    public void setUp() {
        mapper = getXmlMapper();
        resourceLoader = new DefaultResourceLoader();
    }

    /**
     * Verifica la mappatura degli attributi radice del file XML (Namespace, Versione, Schema).
     * <p>
     * Assicura che i metadati fondamentali del formato BMEcat siano letti correttamente
     * nel DTO {@link XmlOrder}.
     * * @throws Exception in caso di errori di I/O o parsing.
     */
    @Test
    public void validateRootAttributes() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);

            XmlOrder dto = mapper.treeToValue(root, XmlOrder.class);
            assertNotNull("DTO after treeToValue should not be null", dto);
            // guardo gli attributi di schema
            assertEquals("XmlOrder has mapped xmlns", root.path("xmlns").toString().replaceAll("\"", ""), dto.getXmlns());
            assertEquals("XmlOrder has mapped xsi", root.path("xmlns:xsi").toString().replaceAll("\"", ""), dto.getXsi());
            assertEquals("XmlOrder has mapped bmecat", root.path("xmlns:bmecat").toString().replaceAll("\"", ""), dto.getBmecat());
            assertEquals("XmlOrder has mapped version", root.path("version").toString().replaceAll("\"", ""), dto.getVersion());
            assertEquals("XmlOrder has mapped type", root.path("type").toString().replaceAll("\"", ""), dto.getType());
            assertEquals("XmlOrder has mapped schema_location", root.path("xsi:schemaLocation").toString().replaceAll("\"", ""), dto.getSchemaLocation());
        }
    }
    
    /**
     * Verifica la deserializzazione della sezione Header (ORDER_HEADER).
     * <p>
     * Controlla: ID ordine, date, valuta, riferimenti alle parti (Buyer, Supplier) e
     * indirizzi di spedizione.
     * * @throws Exception in caso di errori di I/O o parsing.
     */
    @Test
    public void validateHeader() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);
            JsonNode infoNode = root.path("ORDER_HEADER").path("ORDER_INFO");
            XmlOrderInfo xoi = mapper.treeToValue(infoNode, XmlOrderInfo.class);
            assertEquals(infoNode.path("ORDER_ID").toString().replaceAll("\"", ""), xoi.getOrderId());
            assertEquals(infoNode.path("ORDER_DATE").toString().replaceAll("\"", ""), xoi.getOrderDate());
            assertEquals(infoNode.path("bmecat:CURRENCY").toString().replaceAll("\"", ""), xoi.getCurrency());
            JsonNode deliveryDateNode = infoNode.path("DELIVERY_DATE");
            XmlDeliveryDate xdd = xoi.getDeliveryDate();
            assertEquals(deliveryDateNode.path("type").toString().replaceAll("\"", ""), xdd.getType());
            assertEquals(deliveryDateNode.path("DELIVERY_START_DATE").toString().replaceAll("\"", ""), xdd.getDeliveryStartDate());
            assertEquals(deliveryDateNode.path("DELIVERY_END_DATE").toString().replaceAll("\"", ""), xdd.getDeliveryEndDate());
            JsonNode partyNodeList = infoNode.path("PARTIES").path("PARTY");
            assertTrue("PARTIES dev'essere un array", partyNodeList.isArray());
            JsonNode party = partyNodeList.get(0);
            XmlParty xp = mapper.treeToValue(party, XmlParty.class);
            assertEquals(party.path("bmecat:PARTY_ID").path("").toString().replaceAll("\"", ""), xp.getPartyId().getPartyId());
            assertEquals(party.path("bmecat:PARTY_ID").path("type").toString().replaceAll("\"", ""), xp.getPartyId().getType());
            assertEquals(party.path("PARTY_ROLE").toString().replaceAll("\"", ""), xp.getPartyRole());
            JsonNode orderPartiesReference = infoNode.path("ORDER_PARTIES_REFERENCE");
            XmlOrderPartiesReference xopr = xoi.getOrderPartiesReference();
            assertEquals(orderPartiesReference.path("bmecat:BUYER_IDREF").path("").toString().replaceAll("\"", ""), xopr.getBuyerIdRef().getPartyId());
            assertEquals(orderPartiesReference.path("bmecat:BUYER_IDREF").path("type").toString().replaceAll("\"", ""), xopr.getBuyerIdRef().getType());
            assertEquals(orderPartiesReference.path("bmecat:SUPPLIER_IDREF").path("").toString().replaceAll("\"", ""), xopr.getSupplierIdRef().getPartyId());
            assertEquals(orderPartiesReference.path("bmecat:SUPPLIER_IDREF").path("type").toString().replaceAll("\"", ""), xopr.getSupplierIdRef().getType());
            JsonNode shipmentPartiesReference = orderPartiesReference.path("SHIPMENT_PARTIES_REFERENCE");
            XmlShipmentPartiesReference xspr = xopr.getShipmentPartiesRef();
            assertEquals(shipmentPartiesReference.path("DELIVERY_IDREF").path("").toString().replaceAll("\"", ""), xspr.getDeliveryIdRef().getPartyId());
            assertEquals(shipmentPartiesReference.path("DELIVERY_IDREF").path("type").toString().replaceAll("\"", ""), xspr.getDeliveryIdRef().getType());
        }
    }
    
    /**
     * Verifica la deserializzazione delle righe d'ordine (ORDER_ITEM_LIST).
     * <p>
     * Controlla che la lista degli articoli venga letta come array e valida i campi
     * del singolo articolo (Quantità, Unità, ID prodotto, Descrizione).
     * * @throws Exception in caso di errori di I/O o parsing.
     */
    @Test
    public void validateItem() throws Exception{
    	
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);
            JsonNode itemNodeList = root.path("ORDER_ITEM_LIST").path("ORDER_ITEM");
            assertTrue("ORDER_ITEM_LIST dev'essere un array", itemNodeList.isArray());
            JsonNode itemNode = itemNodeList.get(0);
            XmlItem xi = mapper.treeToValue(itemNode, XmlItem.class);
            assertEquals(itemNode.path("QUANTITY").toString().replaceAll("\"", ""), String.valueOf(xi.getQuantity()).substring(0, 2));
            assertEquals(itemNode.path("bmecat:ORDER_UNIT").toString().replaceAll("\"", ""), xi.getOrderUnit());
            assertEquals(itemNode.path("LINE_ITEM_ID").toString().replaceAll("\"", ""), String.valueOf(xi.getLineItemId()));
            JsonNode partyIDNode = itemNode.path("PRODUCT_ID");
            XmlProductID xpid = xi.getProdId();
            assertEquals(partyIDNode.path("bmecat:SUPPLIER_PID").toString().replaceAll("\"", ""), xpid.getSupplierId().getPartyId());
            assertEquals(partyIDNode.path("bmecat:BUYER_PID").path("").toString().replaceAll("\"", ""), xpid.getBuyerId().getPartyId());
            assertEquals(partyIDNode.path("bmecat:BUYER_PID").path("type").toString().replaceAll("\"", ""), xpid.getBuyerId().getType());
            assertEquals(partyIDNode.path("bmecat:DESCRIPTION_SHORT").toString().replaceAll("\"", ""), xpid.getDescriptionShort());
        }
    }
    
    /**
     * Verifica la deserializzazione del sommario finale (ORDER_SUMMARY).
     * * @throws Exception in caso di errori di I/O o parsing.
     */
    @Test
    public void validateSummary() throws Exception {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
            JsonNode root = mapper.readTree(is);
            JsonNode summaryNode = root.path("ORDER_SUMMARY");
            XmlOrderSummary sum = mapper.treeToValue(summaryNode, XmlOrderSummary.class);
            assertEquals(summaryNode.path("TOTAL_ITEM_NUM").toString().replaceAll("\"", ""), String.valueOf(sum.getTotalItemNum()));
        }
    }
    
    /**
     * Test di "Round-Trip" per verificare l'integrità del mapping strutturale.
     * <p>
     * Il test esegue i seguenti passaggi:
     * <ol>
     * <li>Deserializza l'XML in un oggetto DTO {@link XmlOrder}.</li>
     * <li>Ricostruisce manualmente un oggetto di dominio {@link OrderStructure} a partire dai dati del DTO.</li>
     * <li>Utilizza {@link DataMapper} per riconvertire il POJO di dominio in XML.</li>
     * <li>Confronta la stringa XML generata con quella attesa dal DTO originale.</li>
     * </ol>
     * Serve a garantire che la trasformazione DTO -> Domain -> XML non perda informazioni.
     * * @throws IOException in caso di errori di lettura o scrittura.
     */
    @Test
    public void roundTripOrderStructuralEquality_usingDataMapper() throws IOException {
        Resource res = resourceLoader.getResource("classpath:xml/order/ESEMPIO_CASO_REALE.xml");
        assertTrue("resource must exist in classpath: xml/order/ESEMPIO_CASO_REALE.xml", res.exists());

        try (InputStream is = res.getInputStream()) {
        	
            JsonNode root = mapper.readTree(is);
            
            //root
            XmlOrder dto = mapper.treeToValue(root, XmlOrder.class);
            
            //HEADER
            XmlOrderHeader xoh = new XmlOrderHeader();
            JsonNode infoNode = root.path("ORDER_HEADER").path("ORDER_INFO");
            XmlOrderInfo xoi = mapper.treeToValue(infoNode, XmlOrderInfo.class);
            xoh.setOrderInfo(xoi);//aggiungo xoi a xoh
            JsonNode partyNodeList = infoNode.path("PARTIES").path("PARTY");
            List<XmlParty> parties = new ArrayList<>();
            for(JsonNode party : partyNodeList) {
                parties.add(mapper.treeToValue(party, XmlParty.class));
            }
            xoi.setOrderParties(parties);//aggiungo parties a xoi
            
            
            //ITEM
            JsonNode itemNodeList = root.path("ORDER_ITEM_LIST").path("ORDER_ITEM");
            List<XmlItem> items = new ArrayList<>();
            for(JsonNode itemNode : itemNodeList) {
            	items.add(mapper.treeToValue(itemNode, XmlItem.class));
            }
            
            
            //SUMMARY
            JsonNode summaryNode = root.path("ORDER_SUMMARY");
            XmlOrderSummary sum = mapper.treeToValue(summaryNode, XmlOrderSummary.class);
            
            
            //unisco tutti i pezzi
            dto.setOh(xoh);
            dto.setOrderItem(items);
            dto.setOs(sum);
            
            //serializzo dto
            String expected = DataMapper.serializeXmlOrder(dto);
            
            //ricreo OrderStructure
            OrderStructure ostr = new OrderStructure();
            
            //header
            OrderHeader oh = new OrderHeader();
            oh.setOrderID(dto.getOh().getOrderInfo().getOrderId());
            for(XmlParty xp : dto.getOh().getOrderInfo().getOrderParties()) {
            	switch(xp.getPartyRole()) {
            		case "buyer":
            			oh.setBuyerID(xp.getPartyId().getPartyId());
            			break;
            		case "supplier":
            			oh.setSupplierID(xp.getPartyId().getPartyId());
            			break;
            		case "delivery":
	            		oh.setDeliveryID(xp.getPartyId().getPartyId());
	            		break;
	            	default:
	            		fail("Non è un PartyRole!");
            	}
            }
            oh.setBuyerIDRef(dto.getOh().getOrderInfo().getOrderPartiesReference().getBuyerIdRef().getPartyId());
            oh.setSupplierIDRef(dto.getOh().getOrderInfo().getOrderPartiesReference().getSupplierIdRef().getPartyId());
            oh.setDeliveryIDRef(dto.getOh().getOrderInfo().getOrderPartiesReference().getShipmentPartiesRef().getDeliveryIdRef().getPartyId());
            oh.setCurrency(dto.getOh().getOrderInfo().getCurrency());
            oh.setStartDate(dto.getOh().getOrderInfo().getDeliveryDate().getDeliveryStartDate());
            oh.setEndDate(dto.getOh().getOrderInfo().getDeliveryDate().getDeliveryEndDate());
            oh.setOrderDate(dto.getOh().getOrderInfo().getOrderDate());
            ostr.setHeader(oh);
            //items
            OrderItem[] itmsArray = new OrderItem[dto.getOrderItem().size()];
            OrderItem it = null;
            int i = 0;
            for(XmlItem xi : dto.getOrderItem()) {
            	it = new OrderItem();
            	it.setBuyerID(xi.getProdId().getBuyerId().getPartyId());
            	it.setSupplierID(xi.getProdId().getSupplierId().getPartyId());
            	it.setDescriptionShort(xi.getProdId().getDescriptionShort());
            	it.setLineItemID(String.valueOf(xi.getLineItemId()));
            	it.setOrderUnit(xi.getOrderUnit());
            	it.setQuantity(String.valueOf(xi.getQuantity()));
            	itmsArray[i++] = it;
            }
            ostr.setItemList(itmsArray);
            //summary
            OrderSummary os = new OrderSummary();
            os.setTotalItemNum(dto.getOs().getTotalItemNum());
            ostr.setOrderSummary(os);
            
            //serializzo OrderStructure
            String actual = DataMapper.serializeXmlOrder(
            			DataMapper.mapOrderToXml(ostr)
            		);
            
            //comparo le serializzazioni
            assertEquals(expected, actual);
        }
    }
}