package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.util.Map;
import java.util.Optional;

import com.beemediate.beemediate.infrastructure.odoo.mapper.AttributeMapper;

/**
 * DTO che mappa i dettagli prodotto specifici di un certo fornitore. I campi rimappano alcuni attributi richiesti al model <i>product.supplierinfo</i> di Odoo.
 */
public class ProdottoFornitoreDTO{
	
	/**
	 * Mapping di id.
	 */
	private Optional<Integer> id;
	/**
	 * Mapping di product_id
	 */
	private IdentifierDTO productId;
	/**
	 * Mapping di sequence
	 */
	private Optional<Integer> sequence;
	/**
	 * Mapping di product_name
	 */
	private Optional<String> productName;
	/**
	 * Mapping di product_code
	 */
	private Optional<String> productCode;
	/**
	 * Mapping di partner_id
	 */
	private IdentifierDTO partnerId;
	/**
	 * Mapping di product_uom_id
	 */
	private IdentifierDTO productUomId;
	
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
