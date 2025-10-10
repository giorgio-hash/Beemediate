package com.beemediate.beemediate.domain.service;


import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

//import org.jmlspecs.annotation.CodeBigintMath;


import com.beemediate.beemediate.domain.exceptions.UnreachableThresholdException;
import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.pojo.order.Order;
import com.beemediate.beemediate.domain.ports.entrypoint.OaFManagerPort;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.ConfirmationProviderPort;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;

/**
 * Classe principale per la gestione della piattagorma. Implementa OaFManagerPort.
 */
@Service
public class OaFBatchManager implements OaFManagerPort{
	
	/***riferimento al gestore buffer ordini*/
	private /*@ spec_public @*/ final OaFBuffer oaf;
	/***riferimento al ricevitore di conferme*/
	private /*@ spec_public @*/ final ConfirmationProviderPort confirmations;
	/***riferimento al getore FTP*/
	private /*@ spec_public @*/ final FTPHandlerPort ftp;
	/***riferimento al notificatore verso CRM*/
	private /*@ spec_public @*/ final DataSenderPort crm;
	/***numero minimo di Order validi richiesti per l'invio al fornitore*/
	private /*@ spec_public @*/ final int oafBatchThreshold;

	/*@ public invariant oaf!=null; @*/
	/*@ public invariant confirmations!=null; @*/
	/*@ public invariant ftp!=null; @*/
	/*@ public invariant crm!=null; @*/
	/*@ public invariant 0 < oafBatchThreshold <= oaf.getBuffer().capacity() <= Integer.MAX_VALUE; @*/
	
	/**
	 * Costruttore
	 * @param threshold - int
	 * @param oafb - oggetto OaFBuffer
	 * @param c - adattatore ConfirmationProviderPort
	 * @param f - adattatore FTPHandlerPort
	 * @param u - adattatore DataSenderPort
	 * @throws UnreachableThresholdException se la differenza <tt>oafb.capacity()</tt>-threshold>0
	 */
	/*@ public normal_behaviour
	  @ requires oafb!=null & c!=null & f!=null & u!=null;
	  @ requires threshold>0 & oafb.getBuffer().capacity()>=threshold;
	  @ ensures oaf!=null & confirmations!=null & ftp!=null & crm!=null;
	  @ ensures oafBatchThreshold <= oaf.getBuffer().capacity();
	  @ also public exceptional_behaviour
	  @ requires oafb.getBuffer().capacity()>0 & oafb.getBuffer().capacity()<threshold;
	  @ signals_only UnreachableThresholdException; 
	  @ pure
	  @*/
//	@CodeBigintMath
	@Autowired
	public OaFBatchManager(final int threshold,final OaFBuffer oafb,final ConfirmationProviderPort c,final FTPHandlerPort f, DataSenderPort u) throws UnreachableThresholdException{
		
		if(oafb.getBuffer().capacity()<threshold)
			throw new UnreachableThresholdException("Capacit� del buffer di caricamento ordini inferiore alla soglia minima di invio.");
		
		oafBatchThreshold = threshold;
		oaf = oafb;
		confirmations = c;
		ftp = f;
		crm = u;
	}
	
	/*@ public normal_behaviour
	  @ assigns confirmations.newConfirmation, crm.positiveResponse;
	  @ requires confirmations!=null;
	  @ requires crm!=null;
	  @ requires ftp!=null;
	  @ ensures \result>=0;
	  @ diverges true;
	  @*/
//	@CodeBigintMath
	@Override
	public int handleConfirmations() {
		
		Confirmation c;
		int confCount=0;
		
		if(confirmations.fetchConfirmations()) { //almeno una conferma c'?
		
		    //@ loop_writes c,confCount,confirmations.newConfirmation;
			//@ maintaining confCount>=0;
			do {
				c = confirmations.popConfirmation();
				
				if(ftp.archive(c) && ftp.delete(c)) //lazy evaluation
					crm.signalConfirmation(c);
				
				confCount++;
			}while(confirmations.hasConfirmation());
			
		}
		
		return confCount;
	}
	
	//@ public normal_behaviour
	//@ requires oaf!=null & crm!=null & ftp!=null;
	/*@ requires 0<oaf.buffer.size ==> (\forall int j; 0<=j<oaf.buffer.size; oaf.buffer.ordini[j] != null
	  @																		& oaf.buffer.ordini[j].data!=null 
	  @																		& oaf.buffer.ordini[j].quantity!=null
	  @																		& oaf.buffer.ordini[j].orderID!=null
	  @																		& \typeof(oaf.buffer.ordini[j]) == \type(Order));
	  @*/
	/*@ requires oaf.buffer.size<oaf.buffer.ordini.length ==> (\forall int j; oaf.buffer.size<=j<oaf.buffer.ordini.length; oaf.buffer.ordini[j]==null);
	  @*/
	//@ ensures \result>=0;
	//@ ensures \not_modified(oaf,oaf.buffer,oaf.buffer.ordini,oaf.buffer.ordini.length);
//	@CodeBigintMath
	@Override
	public int handleOrders() {
		
		/*@ nullable @*/Order o;		
		int toSend=0; //valuto se la threshold ? superata
		
		if((oaf.loadNewBuffer())>0) {
			
			toSend = oaf.validateBuffer();
			
			
			/*@ loop_invariant  o!=null ==> o.data!=null 
			  @							& o.quantity!=null
			  @							& o.orderID!=null;
			  @*/
			/*@ maintaining 0<oaf.buffer.size ==> (\forall int j; 0<=j<oaf.buffer.size; oaf.buffer.ordini[j] != null
			  @																		& oaf.buffer.ordini[j].data!=null 
			  @																		& oaf.buffer.ordini[j].quantity!=null
			  @																		& oaf.buffer.ordini[j].orderID!=null
			  @																		& \typeof(oaf.buffer.ordini[j]) == \type(Order));
			  @*/
			/*@ maintaining oaf.buffer.size<oaf.buffer.ordini.length ==> (\forall int j; oaf.buffer.size<=j<oaf.buffer.ordini.length; oaf.buffer.ordini[j]==null);
			  @*/
			while(!oaf.getBuffer().isEmpty()){
				
				o = oaf.getBuffer().pop();
				
				//segnala al crm errori di contenuto (non critici)
				if(o.hasContentError()) {
					crm.signalContentError(o);
				}
				
				//segnala al crm errori openTrans (critici) e non manda
				if(o.hasOpenTransError()) {
					crm.signalOpenTransError(o);
				}
				else if(toSend>oafBatchThreshold) { //manda e, se l'operazione non d? errori, segnala al crm
					if(ftp.loadOrder(o)) {
						crm.signalShipped(o);
					}
				}
			}
		}
		return toSend;
	}

}
