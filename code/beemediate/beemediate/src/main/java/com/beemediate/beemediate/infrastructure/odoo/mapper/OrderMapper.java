package com.beemediate.beemediate.infrastructure.odoo.mapper;

import com.beemediate.beemediate.infrastructure.odoo.dto.*;
import com.beemediate.beemediate.domain.pojo.order.*;

public class OrderMapper {
	
	private OrderMapper() {};

	public static OrderStructure map(FornitoreDTO f, PreventivoDTO prev, ArticoloPreventivoDTO[] artpr, ProdottoFornitoreDTO[] prodf, DestinazioneDTO dest, CompagniaDTO comp) {
		
		OrderSummary os = new OrderSummary();
		os.setTotalItemNum(artpr.length);
		
		OrderItem[] oi = mapOrderItemList(artpr,prodf);
		
		OrderHeader oh = mapOrderHeader(f,prev,dest,comp);
		
		OrderStructure ostr = new OrderStructure();
		ostr.setHeader(oh);
		ostr.setItemList(oi);
		
		return ostr;
	}
	
	
	
	
	private static OrderItem[] mapOrderItemList(ArticoloPreventivoDTO[] artpr, ProdottoFornitoreDTO[] prodf) {
		
		OrderItem[] oi = new OrderItem[artpr.length];
		
		
		for(int i=0; i<artpr.length; i++) {
			
			oi[i] = new OrderItem();
			
			//buyerID
			if(prodf[i].getProduct_id().getName().isPresent())
				oi[i].setBuyerID(prodf[i].getProduct_id().getName().get());
			else
				oi[i].setBuyerID("");
			
			//supplierID
			if(prodf[i].getProduct_code().isPresent())
				oi[i].setSupplierID(prodf[i].getProduct_code().get());
			else
				oi[i].setSupplierID("");
			
			//descriptionShort
			if(prodf[i].getProduct_name().isPresent())
				oi[i].setDescriptionShort(prodf[i].getProduct_name().get());
			else
				oi[i].setDescriptionShort("");
			
			//lineItemID
			if(prodf[i].getSequence().isPresent())
				oi[i].setLineItemID(prodf[i].getSequence().get().toString());
			else
				oi[i].setLineItemID("");
			
			//quantity
			if(artpr[i].getProduct_qty().isPresent())
				oi[i].setQuantity(artpr[i].getProduct_qty().get().toString());
			else
				oi[i].setLineItemID("");
			
			//orderUnit
			if(prodf[i].getProduct_uom_id().getName().isPresent())
				oi[i].setOrderUnit(prodf[i].getProduct_uom_id().getName().get());
			else
				oi[i].setOrderUnit("");
		}
		
		return oi;
	}
	
	
	
	
	private static OrderHeader mapOrderHeader(FornitoreDTO f, PreventivoDTO prev, DestinazioneDTO dest, CompagniaDTO comp) {
		
		OrderHeader oh = new OrderHeader();
		
		//orderID
		if(prev.getOrigin().isPresent())
			oh.setOrderID(prev.getOrigin().get());
		else
			oh.setOrderID("");
		
		//orderDate
		if(prev.getDate_order().isPresent())
			oh.setOrderDate(prev.getDate_order().get().toString());
		else
			oh.setOrderDate("");
		
		//currency
		if(prev.getCurrency_id().getName().isPresent())
			oh.setCurrency(prev.getCurrency_id().getName().get());
		else
			oh.setCurrency("");
		
		//buyerID
		if(comp.getCompany_registry().isPresent()) {
			oh.setBuyerID(comp.getCompany_registry().get());
			oh.setBuyerIDRef(comp.getCompany_registry().get());
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
		
		//startDate
		if(prev.getDate_approve().isPresent())
			oh.setStartDate(prev.getDate_approve().get().toString());
		else
			oh.setStartDate("");
		
		//endDate
		if(prev.getDate_planned().isPresent())
			oh.setEndDate(prev.getDate_planned().get().toString());
		else
			oh.setEndDate("");
		
		
		return oh;
	}
}
