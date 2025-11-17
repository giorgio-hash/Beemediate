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
 * DTO che mappa gli articoli contenuti nel preventivo dell'ordine di acquisto. I campi rimappano alcuni attributi richiesti al model <i>purchase.order.line</i> di Odoo.
 */
public class ArticoloPreventivoDTO{
	
	/**
	 * Mapping di id.
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di order_id.
	 */
	private final IdentifierDTO orderId;
	/**
	 * Mapping di product_id.
	 */
	private final IdentifierDTO productId;
	/**
	 * Mapping di product_qty.
	 */
	private final Optional<Double> productQty;
	
	
	/**
	 * Static Factory method che nteragisce col model purchase.order.line di Odoo per estrarre gli articoli contenuti nel preventivo.
	 * @param odoo - OdooApiConfig
	 * @param prv - PreventivoDTO
	 * @return Array di elementi ArticoloPreventivoDTO
	 * @throws InconsistentDTOException
	 * @throws EmptyFetchException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static ArticoloPreventivoDTO[] fromXMLRPC(final OdooApiConfig odoo, final PreventivoDTO prv) throws InconsistentDTOException, EmptyFetchException, XmlRpcException  {
		
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
		requestInfo.put(odoo.FIELDS, Arrays.asList("order_id","product_id","product_qty"));
		res = odoo.readFromModel("purchase.order.line", requestInfo, ids);
		
		if(res.length == 0) throw new EmptyFetchException ("Il preventivo ha articoli, ma non li trovo. Preventivo: " + prv);
		
		//collezione di POJO
		artPrv = new ArticoloPreventivoDTO[res.length];
		for(int i=0; i<res.length; i++) {
			artPrv[i] = new ArticoloPreventivoDTO( (HashMap<String,Object>) res[i] );
		}
		
		return artPrv;
	}
	
	
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>purchase.order.line</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public ArticoloPreventivoDTO( final Map<String, Object> map ) {
		
		id = AttributeMapper.intify( map.get("id") );
		
		orderId = new IdentifierDTO( (Object[]) map.get("order_id") );
		
		productId = new IdentifierDTO( (Object[]) map.get("product_id") );
		
		productQty = AttributeMapper.doublify( map.get("product_qty") );
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
	 * @return oggetto IdentifierDTO con identificativo dell'ordine
	 */
	public IdentifierDTO getOrderId() {
		return orderId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo del prodotto associato a questo articolo.
	 */
	public IdentifierDTO getProductId() {
		return productId;
	}

	/**
	 * 
	 * @return oggetto Optional contenente Double, altrimenti Optional.empty()
	 */
	public Optional<Double> getProductQty() {
		return productQty;
	}

	@Override
	public String toString() {
		return "ArticoloPreventivoDTO [id=" + id + ", order_id=" + orderId + ", product_id=" + productId
				+ ", product_qty=" + productQty + "]";
	}

	
}
