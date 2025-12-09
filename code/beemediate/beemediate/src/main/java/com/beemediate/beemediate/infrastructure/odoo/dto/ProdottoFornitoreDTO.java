package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import org.apache.xmlrpc.XmlRpcException;

import com.beemediate.beemediate.infrastructure.odoo.config.OdooApiConfig;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.EmptyFetchException;
import com.beemediate.beemediate.infrastructure.odoo.exceptions.InconsistentDTOException;
import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dettagli prodotto specifici di un certo fornitore. I campi rimappano alcuni attributi richiesti al model <i>product.supplierinfo</i> di Odoo.
 */
public class ProdottoFornitoreDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di product_id
	 */
	private final IdentifierDTO productId;
	/**
	 * Mapping di sequence
	 */
	private final Optional<Integer> sequence;
	/**
	 * Mapping di product_name
	 */
	private final Optional<String> productName;
	/**
	 * Mapping di product_code
	 */
	private final Optional<String> productCode;
	/**
	 * Mapping di partner_id
	 */
	private final IdentifierDTO partnerId;
	/**
	 * Mapping di product_uom_id
	 */
	private final IdentifierDTO productUomId;
	
	
	/**
	 * Static factory method che interagisce col model product.supplierinfo di Odoo per estrarre i dettagli prodotto specifici di un certo fornitore, per ogni prodotto dato in input.
	 * @param odoo - OdooApiConfig
	 * @param pr - Array di ProdottoDTO
	 * @param f - FornitoreDTO
	 * @return Array di ProdottoFornitoreDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static ProdottoFornitoreDTO[] fromXMLRPC(final OdooApiConfig odoo, final ProdottoDTO[] pr, final FornitoreDTO f) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
		
		if (f == null) throw new InconsistentDTOException("FornitoreDTO null");
		if ( f.getName().isEmpty() ) throw new InconsistentDTOException("Fornitore non ha un nome.");
		if (pr == null) throw new InconsistentDTOException("Lista ProdottoDTO null");
		
		final Object[] ids;
		final Object[] res;
		final ProdottoFornitoreDTO[] prd;
		final List<Object> elems;
		final Map<String, Object> requestInfo = new HashMap<>();
		 
		
		//ora estraggo gli id che fanno riferimento ad un articolo a fornitore
		elems = new ArrayList<>();
		for(ProdottoDTO p : pr) {
			if(  p.getSellerIds().isPresent()  && p.getSellerIds().get().length>0) {
				for(Object o : p.getSellerIds().get() )
					elems.add(o);
			}else
				throw new InconsistentDTOException("Il prodotto non ha nessun id a fornitore: " + p);
		}

		
		//cerco gli ordini a fornitore con tali ID assicuradomi che siano dal catalogo di GEALAN
		ids = odoo.searchFromModel("product.supplierinfo", requestInfo, 
									Arrays.asList(OdooApiConfig.PARTNER_ID_FIELD,"=", f.getName().get() ),
									Arrays.asList("id","in",elems));
		
		if (ids.length == 0) throw new EmptyFetchException("Id prodottoFornitoreDTO non trovati");

		// ora estraggo
		requestInfo.clear();
		requestInfo.put(OdooApiConfig.FIELDS, Arrays.asList("id","product_id","sequence","product_name","product_code",OdooApiConfig.PARTNER_ID_FIELD,"product_uom_id"));
		res = odoo.readFromModel("product.supplierinfo", requestInfo, ids);
		
		if (res.length == 0) throw new EmptyFetchException("Non sono stati trovati i prodotti fornitore");
		
		prd = new ProdottoFornitoreDTO[res.length];
		for(int i=0; i<res.length; i++) {
			prd[i] = new ProdottoFornitoreDTO( (HashMap<String,Object>) res[i] );
		}
		
		return prd;
	}
	
	
	/**
	 * 
	 * @param map - Map contente una tupla del model <i>product.supplierinfo</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ProdottoFornitoreDTO( final Map<String, Object> map ) {
		
		id = AttributeMapper.intify( map.get("id") );
		
		productId = new IdentifierDTO( (Object[]) map.get("product_id") );
		
		sequence = AttributeMapper.intify( map.get("sequence") );
		
		productName = AttributeMapper.stringify( map.get("product_name") );
		
		productCode = AttributeMapper.stringify( map.get("product_code") );
		
		partnerId = new IdentifierDTO( (Object[]) map.get("partner_id"));
		
		productUomId = new IdentifierDTO( (Object[]) map.get("product_uom_id") );
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
	 * @return oggetto IdentifierDTO con identificativo del prodotto.
	 */
	public IdentifierDTO getProductId() {
		return productId;
	}

	/**
	 * 
	 * @return oggetto Optional contenente Integer, altrimenti Optional.empty()
	 */
	public Optional<Integer> getSequence() {
		return sequence;
	}

	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getProductName() {
		return productName;
	}

	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getProductCode() {
		return productCode;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo del fornitore.
	 */
	public IdentifierDTO getPartnerId() {
		return partnerId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo dell'unità di misura per la quantità di prodotto.
	 */
	public IdentifierDTO getProductUomId() {
		return productUomId;
	}


	@Override
	public String toString() {
		return "ProdottoFornitoreDTO [id=" + id + ", product_id=" + productId + ", sequence=" + sequence
				+ ", product_name=" + productName + ", product_code=" + productCode + ", partner_id=" + partnerId
				+ ", product_uom_id=" + productUomId 
				+ "]";
	}
	
	

}
