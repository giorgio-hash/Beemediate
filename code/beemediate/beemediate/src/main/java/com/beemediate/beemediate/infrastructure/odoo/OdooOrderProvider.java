package com.beemediate.beemediate.infrastructure.odoo;

import com.beemediate.beemediate.domain.pojo.order.*;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.infrastructure.odoo.dto.*; 
import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.*;
import com.beemediate.beemediate.infrastructure.odoo.mapper.OrderMapper;

import org.apache.xmlrpc.XmlRpcException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.net.MalformedURLException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import javax.security.auth.login.FailedLoginException;

@Service
public class OdooOrderProvider implements OrderProviderPort{
	
	private Order ordine = null;
	
	private final Logger log = LoggerFactory.getLogger(OdooOrderProvider.class);
	private final OdooApiConfig odoo;
	
	
	@Autowired
	public OdooOrderProvider(OdooApiConfig odoo) {
		this.odoo = odoo;
	}


	
	@Override
	public Order popNewOrder() {
		Order o = ordine;
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
		}catch(MalformedURLException | FailedLoginException | XmlRpcException e){
			log.info(e.getMessage());
		}
		
		return false;
	}
	
	
	
	//******** metodi helper di servizio
	
	private boolean fetchData() throws MalformedURLException, FailedLoginException, XmlRpcException {
		
		// se non si è connessi, prova una connessione.
		if(odoo.isOnline() == false)
			odoo.connect();
		
		
		ordine = null;
		
		try {
			
			FornitoreDTO f = null;
			PreventivoDTO prev = null;
			ArticoloPreventivoDTO[] artpr = null;
			ProdottoFornitoreDTO[] prodf = null;
			DestinazioneDTO dest = null;
			CompagniaDTO comp = null;
			OrderStructure ordstr = null;
			
			
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
		} catch (Exception e4) {
			e4.printStackTrace();
		}
		
		return hasNewOrder();
		
	}
	
	
	
	
	private FornitoreDTO estraiFornitore() throws EmptyFetchException, XmlRpcException {
		Object[] ids = null;
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		//cerca GEALAN
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"res.partner","search",
						Arrays.asList(Arrays.asList(Arrays.asList("name","=","GEALAN"))),
						requestInfo
						)
				);
		
		if(ids.length == 0) throw new EmptyFetchException ("Non trovo GEALAN");
		
		//estrai GEALAN
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("name","ref"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"res.partner","read",
						Arrays.asList(ids),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato GEALAN, ma non riesco ad estrarlo.");
		
		
		return new FornitoreDTO( (HashMap<String, Object>) res[0] );
	}
	
	
	
	
	private PreventivoDTO estraiPreventivo(FornitoreDTO f) throws EmptyFetchException, ClassCastException, XmlRpcException {
		
		Object[] ids = null;
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		//cerca un preventivo di GEALAN
		requestInfo.clear();
		requestInfo.put("limit", 1);
		ids = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList("partner_id","=",f.getName().get()),
								Arrays.asList("x_studio_oaf","=","new")
								)),
						requestInfo
						)
				);
		
		if(ids.length == 0) throw new EmptyFetchException ("Nessun preventivo \"new\" per GEALAN");
		
		//estrai preventivo
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("name","partner_id","product_id","origin","order_line","currency_id","date_order","date_approve","date_planned","picking_type_id","company_id","x_studio_oaf"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order","read",
						Arrays.asList(ids),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato preventivi per GEALAN, ma nessuno estratto.");
		
		return new PreventivoDTO( (HashMap<String, Object>) res[0] ); //n.b. è possibile estrarre più preventivi. Al momento si tratterà un singolo preventivo
	}
	
	
	
	
	private ConsegnaDTO estraiConsegna(PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		if (prv == null) throw new InconsistentDTOException("Oggetto PreventivoDTO null");
		
		Object id = prv.getPicking_type_id().getNum().get();
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("warehouse_id"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.picking.type","read",
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni sulla consegna.");
		
		return new ConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	
	private ContattoConsegnaDTO estraiContattoConsegna(ConsegnaDTO cns) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		if (cns == null) throw new InconsistentDTOException("Oggetto ConsegnaDTO null");
		
		Object id = cns.getWarehouse_id().getNum().get();
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("partner_id"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"stock.warehouse","read",
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni del contatto di consegna.");
		
		return new ContattoConsegnaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	
	private DestinazioneDTO estraiDestinazione(ContattoConsegnaDTO concons) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {

		if (concons == null) throw new InconsistentDTOException("Oggetto ContattoConsegnaDTO null");
		
		Object id = concons.getPartner_id().getNum().get();
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("ref"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"res.partner","read",
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della destinazione.");
		
		return new DestinazioneDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	
	private CompagniaDTO estraiCompagnia(PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		if (prv == null) throw new InconsistentDTOException("Oggetto PreventivoDTO null");
		
		Object id = prv.getPicking_type_id().getNum().get();
		Object[] res = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("ref"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"res.partner","read",
						Arrays.asList(Arrays.asList(id)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Non trovo informazioni della compagnia ");
		
		return new CompagniaDTO( (HashMap<String, Object>) res[0]);
	}
	
	
	
	
	private ArticoloPreventivoDTO[] estraiArticoliPreventivo(PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		if (prv == null) throw new InconsistentDTOException("Oggetto PreventivoDTO null");
		
		Object[] ids = null;
		Object[] res = null;
		ArticoloPreventivoDTO[] art_prv = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		
		if(prv == null)
			throw new InconsistentDTOException("POJO null");
		
		//verifica che il preventivo contenga le sue parti
		if(prv.getOrder_line().isPresent())
			ids = (prv).getOrder_line().get();
		else {
			throw new InconsistentDTOException("Non hai ordini nel preventivo.");
		}
		
		if(ids.length == 0) throw new EmptyFetchException ("Non sono stati trovati articoli nel preventivo " + prv);
		
		//estrai parti del preventivo
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("order_id","product_id","product_qty"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"purchase.order.line","read",
						Arrays.asList(Arrays.asList(ids)),
						requestInfo
						)
				);
		
		if(res.length == 0) throw new EmptyFetchException ("Il preventivo ha articoli, ma non li trovo. Preventivo: " + prv);
		
		//collezione di POJO
		art_prv = new ArticoloPreventivoDTO[res.length];
		for(int i=0; i<res.length; i++) {
			art_prv[i] = new ArticoloPreventivoDTO( (HashMap<String,Object>) res[i] );
		}
		
		return art_prv;
	}
	
	
	
	
	private ProdottoDTO[] estraiProdottoPerArticoloPreventivo(ArticoloPreventivoDTO[] ap) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		if ( ap == null ) throw new InconsistentDTOException("Lista ArticoloPreventivoDTO null");
		
		Object[] ids = new Object[ap.length];
		Object[] res = null;
		ProdottoDTO[] prd = new ProdottoDTO[ap.length];
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		
		//estrai prodotti (per arricchire le info sulle parti del preventivo)
		
		//prima bisogna cercare gli id del prodotto
		for(int i=0; i<ap.length; i++) {
			
			if((ap[i]).getProduct_id().getNum().isEmpty()) throw new InconsistentDTOException("id prodotto non presente. articolo: " + ap[i]);
			
			ids[i] = (ap[i]).getProduct_id().getNum().get();
		}
		
		//estrazione
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("seller_ids"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.product","read",
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
	
	
	
	
	private ProdottoFornitoreDTO[] estraiProdottoFornitore(ProdottoDTO[] pr, FornitoreDTO f) throws InconsistentDTOException, EmptyFetchException, ClassCastException, XmlRpcException  {
		
		
		if (f == null) throw new InconsistentDTOException("FornitoreDTO null");
		if (pr == null) throw new InconsistentDTOException("Lista ProdottoDTO null");
		
		Object[] ids = null;
		Object[] res = null;
		ProdottoFornitoreDTO[] prd = null;
		ArrayList<Object> elems = null;
		HashMap<String, Object> requestInfo = new HashMap<String, Object>();
		 
		
		//ora estraggo gli id che fanno riferimento ad un articolo a fornitore
		elems = new ArrayList<Object>();
		for(int i=0; i<pr.length; i++) {
			if(  pr[i].getSeller_ids().isPresent()  )
				for(Object o : pr[i].getSeller_ids().get() )
					elems.add(o);
			else
				throw new InconsistentDTOException("Il prodotto non ha nessun id a fornitore: " + pr[i]);
		}

		
		if ( f.getName().isEmpty() ) throw new InconsistentDTOException("Fornitore non ha un nome.");
		//cerco gli ordini a fornitore con tali ID assicuradomi che siano dal catalogo di GEALAN
		ids = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.supplierinfo","search",
						Arrays.asList(Arrays.asList(
								Arrays.asList("partner_id","=", f.getName().get() ),
								Arrays.asList("id","in",elems)
								))
						)
				);

		// ora estraggo
		requestInfo.clear();
		requestInfo.put("fields", Arrays.asList("id","product_id","sequence","product_name","product_code","partner_id","product_uom_id"));
		res = (Object[]) odoo.models.execute("execute_kw",
				Arrays.asList(
						odoo.getDb(),odoo.getUid(),odoo.getPassword(),
						"product.supplierinfo","read",
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
