package com.beemediate.beemediate.infrastructure.odoo.mapper;

import com.beemediate.beemediate.infrastructure.odoo.dto.*;
import com.beemediate.beemediate.domain.pojo.order.*;

/**
 * Classe utility per mappare i dati ricevuti da Odoo in un OrderStructure. A tale scopo, la classe si serve delle classi "DTO" presenti in <i>com.beemediate.beemediate.infrastructure.odoo.dto</i>.
 */
public final class OrderMapper {
	
	private OrderMapper() {/*empty constructor*/}

	/**
	 * Crea un OrderStructure utilizzando i dati dei "DTO" forniti in input.
	 * @param f - FornitoreDTO
	 * @param prev - PreventivoDTO
	 * @param artpr - Array di ArticoloPreventivoDTO
	 * @param prodf - Array di ProdottoFornitoreDTO
	 * @param dest - DestinazioneDTO
	 * @param comp - CompagniaDTO
	 * @return OrderStructure
	 */
	public static OrderStructure map(final FornitoreDTO f, final PreventivoDTO prev, final ArticoloPreventivoDTO[] artpr, final ProdottoFornitoreDTO[] prodf, final DestinazioneDTO dest, final CompagniaDTO comp) {
		
		final OrderSummary os = new OrderSummary();
		os.setTotalItemNum(artpr.length);
		
		final OrderItem[] oi = mapOrderItemList(artpr,prodf);
		
		final OrderHeader oh = mapOrderHeader(f,prev,dest,comp);
		
		final OrderStructure ostr = new OrderStructure();
		ostr.setHeader(oh);
		ostr.setItemList(oi);
		ostr.setOrderSummary(os);
		
		return ostr;
	}
	
	
	
	/**
	 * Crea un array di OrderItem utilizzando i dati dei "DTO" forniti in input.
	 * @param artpr - ArticoloPreventivoDTO
	 * @param prodf - ProdottoFornitoreDTO
	 * @return Array di OrderItem
	 */
	private static OrderItem[] mapOrderItemList(final ArticoloPreventivoDTO[] artpr, final ProdottoFornitoreDTO[] prodf) {
		
		final OrderItem[] oi = new OrderItem[artpr.length];
		
		
		for(int i=0; i<artpr.length; i++) {
			
			oi[i] = new OrderItem();
			
			//buyerID
			if(prodf[i].getProductId().getName().isPresent())
				oi[i].setBuyerID(prodf[i].getProductId().getName().get());
			else
				oi[i].setBuyerID("");
			
			//supplierID
			if(prodf[i].getProductCode().isPresent())
				oi[i].setSupplierID(prodf[i].getProductCode().get());
			else
				oi[i].setSupplierID("");
			
			//descriptionShort
			if(prodf[i].getProductName().isPresent())
				oi[i].setDescriptionShort(prodf[i].getProductName().get());
			else
				oi[i].setDescriptionShort("");
			
			//lineItemID
			if(prodf[i].getSequence().isPresent())
				oi[i].setLineItemID(prodf[i].getSequence().get().toString());
			else
				oi[i].setLineItemID("");
			
			//quantity
			if(artpr[i].getProductQty().isPresent())
				oi[i].setQuantity(artpr[i].getProductQty().get().toString());
			else
				oi[i].setLineItemID("");
			
			//orderUnit
			if(prodf[i].getProductUomId().getName().isPresent())
				oi[i].setOrderUnit(prodf[i].getProductUomId().getName().get());
			else
				oi[i].setOrderUnit("");
		}
		
		return oi;
	}
	
	
	
	/**
	 * Crea un OrderHeader utilizzando i dati dei "DTO" forniti in input.
	 * @param f - FornitoreDTO
	 * @param prev - PreventivoDTO
	 * @param dest - DestinazioneDTO
	 * @param comp - CompagniaDTO
	 * @return OrderHeader
	 */
	private static OrderHeader mapOrderHeader(final FornitoreDTO f, final PreventivoDTO prev, final DestinazioneDTO dest, final CompagniaDTO comp) {
		
		final OrderHeader oh = new OrderHeader();
		
		//orderID
		if(prev.getOrigin().isPresent())
			oh.setOrderID(prev.getOrigin().get());
		else
			oh.setOrderID("");
		
		//currency
		if(prev.getCurrencyId().getName().isPresent())
			oh.setCurrency(prev.getCurrencyId().getName().get());
		else
			oh.setCurrency("");
		
		//buyerID
		if(comp.getCompanyRegistry().isPresent()) {
			oh.setBuyerID(comp.getCompanyRegistry().get());
			oh.setBuyerIDRef(comp.getCompanyRegistry().get());
		}else {
			oh.setBuyerID("");
			oh.setBuyerIDRef("");
		}
		
		//supplierID
		if(f.getCodiceAzienda().isPresent()) {
			oh.setSupplierID(f.getCodiceAzienda().get());
			oh.setSupplierIDRef(f.getCodiceAzienda().get());
		}else {
			oh.setSupplierID("");
			oh.setSupplierIDRef("");
		}
		
		//deliveryID
		//deliveryIDRef
		if(dest.getCodiceDestinazione().isPresent()) {
			oh.setDeliveryID(dest.getCodiceDestinazione().get());
			oh.setDeliveryIDRef(dest.getCodiceDestinazione().get());
		}else {
			oh.setDeliveryID("");
			oh.setDeliveryIDRef("");
		}
		
		//orderDate
		if(prev.getDateOrder().isPresent())
			oh.setOrderDate(prev.getDateOrder().get().toString());
		else
			oh.setOrderDate("");
		
		//startDate
		if(prev.getDateApprove().isPresent())
			oh.setStartDate(prev.getDatePlanned().get().toString());
		else
			oh.setStartDate("");
		
		//endDate
		if(prev.getDatePlanned().isPresent())
			oh.setEndDate(prev.getDatePlanned().get().toString());
		else
			oh.setEndDate("");
		
		
		return oh;
	}
}
