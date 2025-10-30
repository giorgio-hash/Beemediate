package com.beemediate.beemediate.infrastructure.odoo.dto;

import java.time.LocalDateTime;
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
 * DTO che mappa informazioni sul preventivo per la fornitura. I campi rimappano alcuni attributi richiesti al model <i>purchase.order</i> di Odoo.
 */
public class PreventivoDTO{
	
	/**
	 * Mapping di id
	 */
	private final Optional<Integer> id;
	/**
	 * Mapping di name
	 */
	private final Optional<String> name;
	/**
	 * Mapping di partner_id
	 */
	private final IdentifierDTO partnerId;
	/**
	 * Mapping di product_id
	 */
	private final IdentifierDTO productId;
	/**
	 * Mapping di currency_id
	 */
	private final IdentifierDTO currencyId;
	/**
	 * Mapping di picking_type_id
	 */
	private final IdentifierDTO pickingTypeId;
	/**
	 * Mapping di company_id
	 */
	private final IdentifierDTO companyId;
	/**
	 * Mapping di origin
	 */
	private final Optional<String> origin;
	/**
	 * Mapping di order_line
	 */
	private final Optional<Object[]> orderLine;
	/**
	 * Mapping di date_order
	 */
	private final Optional<LocalDateTime> dateOrder;
	/**
	 * Mapping di date_approve
	 */
	private final Optional<LocalDateTime> dateApprove;
	/**
	 * Mapping di date_planned
	 */
	private final Optional<LocalDateTime> datePlanned;
	
	
	/**
	 * Static factory method che interagisce col model purchase.order di Odoo per estrarre informazioni sul preventivo per la fornitura.
	 * @param odoo - OdooApiConfig
	 * @param f - FornitoreDTO
	 * @return PreventivoDTO
	 * @throws EmptyFetchException
	 * @throws InconsistentDTOException
	 * @throws ClassCastException
	 * @throws XmlRpcException
	 */
	public static PreventivoDTO fromXMLRPC(final OdooApiConfig odoo, final FornitoreDTO f) throws EmptyFetchException, InconsistentDTOException, XmlRpcException {
		
		Object[] ids;
		Object[] res;
		final Map<String, Object> requestInfo = new HashMap<>();
		
		if (f == null || f.getName().isEmpty()) throw new InconsistentDTOException("Oggetto FornitoreDTO non ha le informazioni necessarie");
		
		//cerca un preventivo di GEALAN
		requestInfo.clear();
		requestInfo.put("limit", 1);
		ids = odoo.searchFromModel("purchase.order", requestInfo, 
									Arrays.asList(odoo.PARTNER_ID_FIELD,"=",f.getName().get()),
									Arrays.asList("x_studio_oaf","=",OdooApiConfig.OafStatus.NEW.toString() ));
		
		if(ids.length == 0) throw new EmptyFetchException ("Nessun preventivo \"new\" per GEALAN");
		
		//estrai preventivo
		requestInfo.clear();
		requestInfo.put(odoo.FIELDS, Arrays.asList("name",odoo.PARTNER_ID_FIELD,"product_id","origin","order_line","currency_id","date_order","date_approve","date_planned","picking_type_id","company_id","x_studio_oaf"));
		res = odoo.readFromModel("purchase.order", requestInfo, ids);
		
		if(res.length == 0) throw new EmptyFetchException ("Trovato preventivi per GEALAN, ma nessuno estratto.");
		
		return new PreventivoDTO( (HashMap<String, Object>) res[0] ); //n.b. è possibile estrarre più preventivi. Al momento si tratterà un singolo preventivo
	}
	
	/**
	 * Costruttore
	 * @param map - Map contente una tupla del model <i>purchase.order</i> di Odoo. Ogni coppia chiave-valore fa riferimento ad un attributo del model.
	 */
	public PreventivoDTO( final Map<String, Object> map) {
		
		id = AttributeMapper.intify(map.get("id"));
		
		name = AttributeMapper.stringify(map.get("name"));
		
		partnerId = new IdentifierDTO( (Object[]) map.get("partner_id") );
		
		productId = new IdentifierDTO( (Object[]) map.get("product_id") );
		
		currencyId = new IdentifierDTO( (Object[]) map.get("currency_id") );
		
		pickingTypeId = new IdentifierDTO( (Object[]) map.get("picking_type_id") );
		
		companyId = new IdentifierDTO( (Object[]) map.get("company_id") );
		
		origin = AttributeMapper.stringify( map.get("origin") );
		
		orderLine = AttributeMapper.toArray( map.get("order_line") );
		
		dateOrder = AttributeMapper.toLocalDateTime( map.get("date_order") );
		
		dateApprove = AttributeMapper.toLocalDateTime( map.get("date_approve") );
		
		datePlanned = AttributeMapper.toLocalDateTime( map.get("date_planned") );
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
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getName() {
		return name;
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
	 * @return oggetto IdentifierDTO con identificativo del prodotto che ha attivato il preventivo.
	 */
	public IdentifierDTO getProductId() {
		return productId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo della valuta specificata nel preventivo.
	 */
	public IdentifierDTO getCurrencyId() {
		return currencyId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo della "procedura di consegna" specificato nel preventivo.
	 */
	public IdentifierDTO getPickingTypeId() {
		return pickingTypeId;
	}

	/**
	 * 
	 * @return oggetto IdentifierDTO con identificativo della compagnia cliente del preventivo.
	 */
	public IdentifierDTO getCompanyId() {
		return companyId;
	}

	/**
	 * 
	 * @return oggetto Optional contenente String, altrimenti Optional.empty()
	 */
	public Optional<String> getOrigin() {
		return origin;
	}

	/**
	 * 
	 * @return oggetto Optional contenente Object[], altrimenti Optional.empty()
	 */
	public Optional<Object[]> getOrderLine() {
		return orderLine;
	}

	/**
	 * 
	 * @return oggetto Optional contenente LocalDateTime, altrimenti Optional.empty()
	 */
	public Optional<LocalDateTime> getDateOrder() {
		return dateOrder;
	}

	/**
	 * 
	 * @return oggetto Optional contenente LocalDateTime, altrimenti Optional.empty()
	 */
	public Optional<LocalDateTime> getDateApprove() {
		return dateApprove;
	}

	/**
	 * 
	 * @return oggetto Optional contenente LocalDateTime, altrimenti Optional.empty()
	 */
	public Optional<LocalDateTime> getDatePlanned() {
		return datePlanned;
	}

	@Override
	public String toString() {
		return "PreventivoDTO [id=" + id + ", name=" + name + ", partner_id=" + partnerId + ", product_id="
				+ productId + ", currency_id=" + currencyId + ", picking_type_id=" + pickingTypeId + ", company_id="
				+ companyId + ", origin=" + origin + ", order_line=" + orderLine + ", date_order=" + dateOrder
				+ ", date_approve=" + dateApprove + ", date_planned=" + datePlanned 
				+  "]";
	}
	
	
	
}
