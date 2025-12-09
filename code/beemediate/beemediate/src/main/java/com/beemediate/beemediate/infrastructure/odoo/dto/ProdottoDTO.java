package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;
import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dettagli di un prodotto. I campi rimappano alcuni attributi richiesti al model <i>product.product</i> di Odoo.
 */
public class ProdottoDTO{
	
	/**
	 * Mapping di id
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di seller_ids
	 */
	private final Optional<Object[]> sellerIds;
	
	
	/**
	 * Static factory method che interagisce col model product.product di Odoo per estrarre i dettagli prodotto di ogni articolo contenuto nel preventivo.
	 * @param odoo - OdooApiConfig
	 * @param ap - Array di ArticoloPreventivoDTO
	 * @return Array di elementi ProdottoDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static ProdottoDTO[] fromXMLRPC(final OdooApiConfig odoo, final ArticoloPreventivoDTO[] ap) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
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
		requestInfo.put(OdooApiConfig.FIELDS, Arrays.asList("seller_ids"));
		res = odoo.readFromModel("product.product", requestInfo, ids);
		
		if(res.length==0) {
			StringBuilder sb = new StringBuilder();
			
			for( ArticoloPreventivoDTO p : ap)
				sb.append(p.toString()).append('\n');
			
			throw new EmptyFetchException("Non è stato possibile trovare alcun prodotto associato agli articoli: " + sb.toString());
		}
		
		//collezione di POJO
		for(int i=0; i<res.length; i++) {
			prd[i] = new ProdottoDTO( (HashMap<String,Object>) res[i]);
		}
		
		return prd;
	}
	
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>product.product</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ProdottoDTO( final Map<String, Object> map) {
		
		id = AttributeMapper.intify(map.get("id"));
		
		sellerIds = AttributeMapper.toArray(map.get("seller_ids"));
	}

	/**
	 * 
	 * @return oggetto Optional contenente Integer, altrimenti Optional.empty()
	 */
	public Optional<Integer> getId() {
		return id;
	}

	/**
	 * 
	 * @return oggetto Optional contenente Object[], altrimenti Optional.empty()
	 */
	public Optional<Object[]> getSellerIds() {
		return sellerIds;
	}

	@Override
	public String toString() {
		return "ProdottoDTO [id=" + id + ", seller_ids=" + sellerIds + "]";
	}
	
	
	
}
