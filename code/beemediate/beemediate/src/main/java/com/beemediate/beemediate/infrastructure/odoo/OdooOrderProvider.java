package com.beemediate.beemediate.infrastructure.odoo;

import com.beemediate.beemediate.config.odoo.OdooApiConfig;
import com.beemediate.beemediate.domain.pojo.order.*;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.infrastructure.odoo.dto.*;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.*;
import com.beemediate.beemediate.infrastructure.odoo.mapper.OrderMapper;

import org.apache.xmlrpc.XmlRpcException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.security.auth.login.FailedLoginException;

/**
 * Adattatore che implementa OrderProviderPort. Recupera gli ordini di acquisto dal CRM Odoo, ricostruisce i corrispondenti Order e li conserva in un buffer.
 */
@Component
public class OdooOrderProvider implements OrderProviderPort{
	
	/**
	 * Buffer con singolo elemento Order.
	 */
	private Order ordine = null;
	
	/***riferimento a Logger*/
	private final Logger log = LoggerFactory.getLogger(OdooOrderProvider.class);
	/***Riferimento a Configurazione per autenticazione e comunicazione con CRM Odoo usando il protocollo XML-RPC.*/
	private final OdooApiConfig odoo;
	
	/**
	 * String che identifica il comando RPC per l'esecuzione di procedura remota
	 */
	private static final String EXECUTE_KW = "execute_kw";
	
	/**
	 * String che identifica il model dei contatti su model
	 */
	private static final String CONTACTS_MODEL = "res.partner";
	
	/**
	 * String per l'header utile a specificare i campi di un model
	 */
	private static final String FIELDS = "fields";
	
	/**
	 * String che identifica l'operazione di lettura su model
	 */
	private static final String READ_OP = "read";
	
	/**
	 * String con campo identificativo di un partner dal model
	 */
	private static final String PARTNER_ID_FIELD = "partner_id";
	
	
	/**
	 * Costruttore
	 * @param odoo - configurazione per autenticazione e comunicazione con Odoo via XML-RPC
	 */
	@Autowired
	public OdooOrderProvider(final OdooApiConfig odoo) {
		this.odoo = odoo;
	}


	
	@Override
	public Order popNewOrder() {
		final Order o = ordine;
		ordine = null;
		return o;
	}



	@Override
	public boolean hasNewOrder() {
		return ordine == null;
	}



	@Override
	public boolean fetchOrders() {
		 
		ordine = null;
		
		try {
			return fetchData();
		}catch(MalformedURLException | FailedLoginException | XmlRpcException | URISyntaxException e){
			log.info(e.getMessage());
		}
		
		return false;
	}
	
	
	//*******************************************//	
	//******** metodi helper di servizio ********//
	//*******************************************//
	
	
	/**
	 * Richiede via XML-RPC le informazioni dei model di Odoo e ricostruisce l'oggetto Order.
	 * @return <i>true</i> se viene creato un nuovo Order.
	 * @throws MalformedURLException
	 * @throws FailedLoginException
	 * @throws XmlRpcException
	 * @throws URISyntaxException 
	 */
	private boolean fetchData() throws FailedLoginException, XmlRpcException, URISyntaxException, MalformedURLException {
		
		// se non si è connessi, prova una connessione.
		if(!odoo.isOnline())
			odoo.connect();
		
		
		ordine = null;
		
		try {
			
			final FornitoreDTO f;
			final PreventivoDTO prev;
			final ArticoloPreventivoDTO[] artpr;
			final ProdottoFornitoreDTO[] prodf;
			final DestinazioneDTO dest;
			final CompagniaDTO comp;
			final OrderStructure ordstr;
			
			
			//trova ed estrai GEALAN (e stampa su log)
			f = estraiFornitore();
			log.info(f.toString());
			
			
			//trova ed estrai preventivo (e stampa su log)
			prev = estraiPreventivo(f);
			log.info(prev.toString());
			
			
			//trova informazioni sulla delivery specificata nel preventivo (e stampa su log)
			dest = estraiDestinazione(estraiContattoConsegna(estraiConsegna(prev)));
			log.info(dest.toString());
			
			//trova informazioni sulla compagnia cliente (e stampa su log)
			comp = estraiCompagnia(prev);
			log.info(comp.toString());
			
			//trova ed estrai parti del preventivo (e stampa su log)
			artpr = estraiArticoliPreventivo(prev);
			for(ArticoloPreventivoDTO p : artpr) {
				log.info(p.toString());
			}
			
			//per ogni prodotto associato ad una parte del preventivo, trova ed estrai info su catalogo fornitore (e stampa su log)
			prodf = estraiProdottoFornitore(estraiProdottoPerArticoloPreventivo(artpr),f);
			for(ProdottoFornitoreDTO p : prodf) {
				log.info(p.toString());
			}
			
			//costruzione struct ordine
			ordstr=OrderMapper.map(f, prev, artpr, prodf, dest, comp);
			log.info(ordine.toString());
			//costruzione ordine
			ordine = new Order(ordstr, ordstr.getHeader().getOrderID() );
			
			
		} catch (EmptyFetchException | InconsistentDTOException | ClassCastException e1) {
			log.info(e1.getMessage());
		} 
		
		return hasNewOrder();
		
	}
	
	
	
	/**
	 * Interagisce col model res.partner di Odoo per recuperare le informazioni di contatto fornitore.
	 * @return FornitoreDTO
	 * @throws EmptyFetchException
	 * @throws XmlRpcException
	 */
	private FornitoreDTO estraiFornitore() throws EmptyFetchException, XmlRpcException {
		Object[] ids;
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		//cerca GEALAN
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						CONTACTS_MODEL,"search",
						Arrays.asList(Arrays.asList(Arrays.asList("name","=","GEALAN"))),
						requestInfo
						)
				);
		
		if(ids.length == 0) throw new EmptyFetchException ("Non trovo GEALAN");
		
		//estrai GEALAN
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("name","ref"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						CONTACTS_MODEL,READ_OP,
						Arrays.asList(ids),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato GEALAN, ma non riesco ad estrarlo.");
		
		
		return new FornitoreDTO( (HashMap<String, Object>) res[0] );
	}
	
	
	
	/**
	 * Interagisce col model purchase.order di Odoo per estrarre informazioni sul preventivo per la fornitura.
	 * @param f - FornitoreDTO
	 * @return PreventivoDTO
	 * @throws EmptyFetchException
	 * @throws InconsistentDTOException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private PreventivoDTO estraiPreventivo(final FornitoreDTO f) throws EmptyFetchException, InconsistentDTOException, XmlRpcException {
		
		Object[] ids;
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		if (f == null || f.getName().isEmpty()) throw new InconsistentDTOException("Oggetto FornitoreDTO non ha le informazioni necessarie");
		
		//cerca un preventivo di GEALAN
		requestInfo.clear();
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList(PARTNER_ID_FIELD,"=",f.getName().get()),
								Arrays.asList("x_studio_oaf","=",OdooApiConfig
																	.OafStatus
																	.NEW.toString() )
								)),
						requestInfo
						)
				);
		
		if(ids.length == 0) throw new EmptyFetchException ("Nessun preventivo \"new\" per GEALAN");
		
		//estrai preventivo
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("name",PARTNER_ID_FIELD,"product_id","origin","order_line","currency_id","date_order","date_approve","date_planned","picking_type_id","company_id","x_studio_oaf"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order",READ_OP,
						Arrays.asList(ids),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato preventivi per GEALAN, ma nessuno estratto.");
		
		return new PreventivoDTO( (HashMap<String, Object>) res[0] ); //n.b. è possibile estrarre più preventivi. Al momento si tratterà un singolo preventivo
	}
	
	
	
	/**
	 * Interagisce col model stock.picking.type di Odoo per estrarre il luogo di consegna definito nel preventivo.
	 * @param prv - PreventivoDTO
	 * @return ConsegnaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private ConsegnaDTO estraiConsegna(final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (prv == null || prv.getPickingTypeId().getNum().isEmpty()) throw new InconsistentDTOException("Oggetto PreventivoDTO non ha le informazioni necessarie");
		
		final Object id = prv.getPickingTypeId().getNum().get();
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("warehouse_id"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.picking.type",READ_OP,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni sulla consegna.");
		
		return new ConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	/**
	 * Interagisce col model stock.warehouse di Odoo per estrarre i dettagli relativi al luogo di consegna.
	 * @param cns - ConsegnaDTO
	 * @return ContattoConsegnaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private ContattoConsegnaDTO estraiContattoConsegna(final ConsegnaDTO cns) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (cns == null || cns.getWarehouseId().getNum().isEmpty()) throw new InconsistentDTOException("Oggetto ConsegnaDTO non ha le informazioni necessarie");
		
		final Object id = cns.getWarehouseId().getNum().get();
		final Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList(PARTNER_ID_FIELD));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.warehouse",READ_OP,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni del contatto di consegna.");
		
		return new ContattoConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	/**
	 * Interagisce col model res.partner di Odoo per estrarre informazioni di contatto relative al luogo di consegna.
	 * @param concons - ContattoConsegnaDTO
	 * @return DestinazioneDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private DestinazioneDTO estraiDestinazione(final ContattoConsegnaDTO concons) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {

		if (concons == null || concons.getPartnerId().getNum().isEmpty() ) throw new InconsistentDTOException("Oggetto ContattoConsegnaDTO non ha le informazioni necessarie");
		
		final Object id = concons.getPartnerId().getNum().get();
		final Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("ref"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						CONTACTS_MODEL,READ_OP,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della destinazione.");
		
		return new DestinazioneDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	/**
	 * Interagisce col model res.partner per estrarre informazioni di contatto della compagnia cliente, secondo il preventivo.
	 * @param prv - PreventivoDTO
	 * @return CompagniaDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private CompagniaDTO estraiCompagnia(final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (prv == null || prv.getPickingTypeId().getNum().isEmpty() ) throw new InconsistentDTOException("Oggetto PreventivoDTO non ha le informazioni necessarie");
		
		final Object id = prv.getPickingTypeId().getNum().get();
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("ref"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						CONTACTS_MODEL,READ_OP,
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della compagnia ");
		
		return new CompagniaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	/**
	 * Interagisce col model purchase.order.line di Odoo per estrarre gli articoli contenuti nel preventivo.
	 * @param prv - PreventivoDTO
	 * @return Array di elementi ArticoloPreventivoDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private ArticoloPreventivoDTO[] estraiArticoliPreventivo(final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if (prv == null || prv.getOrderLine().isEmpty() ) throw new InconsistentDTOException("Oggetto PreventivoDTO non ha le informazioni necessarie");
		
		Object[] ids;
		Object[] res;
		ArticoloPreventivoDTO[] artPrv;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		
		
		//verifica che il preventivo contenga le sue parti
		ids = prv.getOrderLine().get();
		
		if(ids.length == 0) throw new EmptyFetchException ("Non sono stati trovati articoli nel preventivo " + prv);
		
		//estrai parti del preventivo
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("order_id","product_id","product_qty"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order.line",READ_OP,
						Arrays.asList(Arrays.asList(ids)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Il preventivo ha articoli, ma non li trovo. Preventivo: " + prv);
		
		//collezione di POJO
		artPrv = new ArticoloPreventivoDTO[res.length];
		for(int i=0; i<res.length; i++) {
			artPrv[i] = new ArticoloPreventivoDTO( (HashMap<String,Object>) res[i] );
		}
		
		return artPrv;
	}
	
	
	
	/**
	 * Interagisce col model product.product di Odoo per estrarre i dettagli prodotto di ogni articolo contenuto nel preventivo.
	 * @param ap - Array di ArticoloPreventivoDTO
	 * @return Array di elementi ProdottoDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private ProdottoDTO[] estraiProdottoPerArticoloPreventivo(final ArticoloPreventivoDTO[] ap) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		if ( ap == null ) throw new InconsistentDTOException("Lista ArticoloPreventivoDTO null");
		
		final Object[] ids = new Object[ap.length];
		Object[] res;
		final ProdottoDTO[] prd = new ProdottoDTO[ap.length];
		final Map<String, Object> requestInfo = new HashMap<>();
		
		//estrai prodotti (per arricchire le info sulle parti del preventivo)
		
		//prima bisogna cercare gli id del prodotto
		for(int i=0; i<ap.length; i++) {
			
			if(ap[i].getProductId().getNum().isEmpty()) 
				throw new InconsistentDTOException("id prodotto non presente. articolo: " + ap[i]);
			else
				ids[i] = ap[i].getProductId().getNum().get();
		}
		
		//estrazione
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("seller_ids"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.product",READ_OP,
						Arrays.asList(Arrays.asList(ids)),
						requestInfo
						)
				);
		
		if(res.length==0) {
			String s = "";
			
			for( ArticoloPreventivoDTO p : ap)
				s += p.toString() + "\n"; 
			
			throw new EmptyFetchException("Non è stato possibile trovare alcun prodotto associato agli articoli: " + s);
		}
		
		//collezione di POJO
		for(int i=0; i<res.length; i++) {
			prd[i] = new ProdottoDTO( (HashMap<String,Object>) res[i]);
		}
		
		return prd;
	}
	
	
	
	/**
	 * Interagisce col model product.supplierinfo di Odoo per estrarre i dettagli prodotto specifici di un certo fornitore, per ogni prodotto dato in input.
	 * @param pr - Array di ProdottoDTO
	 * @param f - FornitoreDTO
	 * @return Array di ProdottoFornitoreDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	private ProdottoFornitoreDTO[] estraiProdottoFornitore(final ProdottoDTO[] pr, final FornitoreDTO f) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		
		if (f == null) throw new InconsistentDTOException("FornitoreDTO null");
		if (pr == null) throw new InconsistentDTOException("Lista ProdottoDTO null");
		
		final Object[] ids;
		final Object[] res;
		final ProdottoFornitoreDTO[] prd;
		final List<Object> elems;
		final Map<String, Object> requestInfo = new HashMap<>();
		 
		
		//ora estraggo gli id che fanno riferimento ad un articolo a fornitore
		elems = new ArrayList<>();
		for(ProdottoDTO p : pr) {
			if(  p.getSellerIds().isPresent()  ) {
				if(p.getSellerIds().isEmpty())
					throw new InconsistentDTOException("ProdottoDTO ha sellerIds vuoto");
				for(Object o : p.getSellerIds().get() )
					elems.add(o);
			}else
				throw new InconsistentDTOException("Il prodotto non ha nessun id a fornitore: " + p);
		}

		
		if ( f.getName().isEmpty() ) throw new InconsistentDTOException("Fornitore non ha un nome.");
		//cerco gli ordini a fornitore con tali ID assicuradomi che siano dal catalogo di GEALAN
		ids = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.supplierinfo","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList(PARTNER_ID_FIELD,"=", f.getName().get() ),
								Arrays.asList("id","in",elems)
								))
						)
				);

		// ora estraggo
		requestInfo.clear();
		requestInfo.put(FIELDS, Arrays.asList("id","product_id","sequence","product_name","product_code",PARTNER_ID_FIELD,"product_uom_id"));
		res = (Object[]) odoo.models.execute(EXECUTE_KW,
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.supplierinfo",READ_OP,
						Arrays.asList(Arrays.asList(ids)),
						requestInfo
						)
				);
		
		prd = new ProdottoFornitoreDTO[res.length];
		for(int i=0; i<res.length; i++) {
			prd[i] = new ProdottoFornitoreDTO( (HashMap<String,Object>) res[i] );
		}
		
		return prd;
	}


}
