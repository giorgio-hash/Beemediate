asm integrazione

import ./STDL/StandardLibrary
import ./STDL/CTLLibrary
import ./STDL/LTLLibrary

signature:

	//******************DOMINI PER IL SERVIZIO******************
	enum domain ServiceState = {NO_ORDER|ORDER}
	enum domain GEALANOperation = {WITHDRAW_ORDER|CONFIRM_ORDER|OFFLINE}
	enum domain Signal = {OPENTRANS_ERROR|CONTENT_ERROR|ODA_CONFIRMATION}
	domain DiscreteIntDomain subsetof Integer //per le LTL/CTL
	//*************************************************
	
	
	
	//******************DOMINI PER L'XML******************
	abstract domain ConstrainedField //hanno un valore obbligatorio
	abstract domain NonemptyField //non possono stare vuoti 
	abstract domain QuantityField //esprimono una quantità 
	
	enum domain QuantityFieldValue = {FLOAT_WITH_COMMA|FLOAT_WITH_DOT|INTEGER|NAN} // GEALAN vuole FLOAT_WITH_DOT
	//*************************************************

	//******************FUNZIONI PER IL SERVIZIO******************
	monitored ftpGEALAN : GEALANOperation
	monitored state : ServiceState

	//gestione segnali
	controlled raisedSignal: Signal -> Boolean

	//gestione FTP
	controlled inboundMessages : DiscreteIntDomain
	controlled outboundMessages : DiscreteIntDomain
	controlled archivedOutboundMessages : DiscreteIntDomain
	//***************************************************************

	//******************FUNZIONI PER L'XML******************
	//diverse combinazioni di questi campi generano diversi tipi di errore
	//	- Content Error, il contenuto verrà caricato su GEALAN ma con valori che andranno corretti in seguito
	//			\__ da minimizzare
	//  - openTransError, il contenuto non verrà caricato su GEALAN
	//			\__ da evitare
	 
	static customer_number : ConstrainedField	
	// sarebbe PARTY_ID in PARTIES/PARTY con PARTY_ROLE=buyer
	//	\__se lasciato vuoto o errato, causa OpenTrans error
	static article_number : ConstrainedField
	//	\__se lasciato vuoto o errato, causa ContentError
	static quantity_measure : ConstrainedField
	//	\__se lasciato vuoto o errato, causa Content error
	static quantity : QuantityField
	//	\__se diverso da FLOAT_WITH_DOT, causa OpenTrans error
	static delivery_location_number : ConstrainedField
	//	\__se lasciato vuoto o errato, causa OpenTrans error
	static delivery_date : NonemptyField
	//	\__se lasciato vuoto, causa OpenTrans error 
	static delivery_date_content : ConstrainedField
	// sarebbe il contenuto nel caso delivery_date fosse True
	//	\__se errato (ad es. data nel passato), causa Content error

	monitored hasRightValue : ConstrainedField -> Boolean
	monitored hasContent : NonemptyField -> Boolean 
	monitored hasQuantity : QuantityField -> QuantityFieldValue

	
	//funzioni derivate per il calcolo degli errori
	derived checkOpenTransError : Boolean
	derived checkContentError : Boolean
	//*************************************************


definitions:

	domain DiscreteIntDomain = {0:100}

	// FUNZIONI 
	
	// verifica la presenza di un'errore OpenTrans ed impedisce il caricamento. Vedi "FUNZIONI PER L'XML" nella sezione "signature"
	function checkOpenTransError = 
							not hasRightValue(customer_number)
							or not hasRightValue(delivery_location_number)
							or not hasContent(delivery_date)
							or hasQuantity(quantity) != FLOAT_WITH_DOT
							
	// verifica la presenza di un'errore ContentError. Vedi "FUNZIONI PER L'XML" nella sezione "signature"
	function checkContentError = 
							not hasRightValue(article_number)
							or not hasRightValue(quantity_measure)
							or implies(hasContent(delivery_date), not hasRightValue(delivery_date_content))
							
	//-------------------------------------------------
	
	
	// REGOLE
	
	rule r_calculateErrors = 
		forall $s in Signal with $s!=ODA_CONFIRMATION do
			switch $s
				case OPENTRANS_ERROR :
					raisedSignal($s) := checkOpenTransError
				case CONTENT_ERROR :
					raisedSignal($s) := checkContentError
			endswitch
					
		
	rule r_sendOrder =
		if not(checkOpenTransError) then
			inboundMessages := inboundMessages + 1
		endif

		
	rule r_checkConfirmation =
		if outboundMessages>0 then
			seq
				archivedOutboundMessages := archivedOutboundMessages + outboundMessages
				outboundMessages := 0
				raisedSignal(ODA_CONFIRMATION) := true
			endseq
		else
			raisedSignal(ODA_CONFIRMATION) := false
		endif



	rule r_resetSignalsExcept($signal in Signal) = forall $s in Signal with $s!=$signal do raisedSignal($s):=false
	
	rule r_resetSignals = forall $s in Signal do raisedSignal($s):=false	
	
	rule r_ftpInteraction =
			switch ftpGEALAN
				case WITHDRAW_ORDER :
					par
						inboundMessages := 0
						r_resetSignalsExcept[ODA_CONFIRMATION]
						r_checkConfirmation[]
					endpar
				case CONFIRM_ORDER :
					par
						r_resetSignals[]
						outboundMessages := outboundMessages + 1
					endpar
				case OFFLINE :
					par
						r_resetSignalsExcept[ODA_CONFIRMATION]
						r_checkConfirmation[]
					endpar
			endswitch
	
	//-------------------------------------------------
	
	
	// INVARIANTI
	// Se una conferma viene letta e poi archiviata, occrre saperlo
	invariant inv_archived over raisedSignal, archivedOutboundMessages : archivedOutboundMessages=0 implies not(raisedSignal(ODA_CONFIRMATION))
	// Il segnale di conferma OdA implica che le conferme sono state archiviate
	invariant inv_confirmed over raisedSignal, archivedOutboundMessages, outboundMessages : raisedSignal(ODA_CONFIRMATION) implies (outboundMessages=0 and archivedOutboundMessages>0)  
	//-------------------------------------------------
	
	
	// LTL/CTL
	//perchè inbound sia caricato, devono valere le seguenti condizioni: state=ORDER e not opentranserror
	//In altre parole: lo stato precedente ha avuto come input ORDER e non ha segnalato OPENTRANS_ERROR
	LTLSPEC g( 
			(y(inboundMessages=0) and inboundMessages>0) 
			implies 
			( y(state=ORDER) and not(raisedSignal(OPENTRANS_ERROR)) )
	)
	//contenterror non impedisce il caricamento. Esistono stati con state=ORDER in cui ottengo contenterror ma carico comunque inbound.
	CTLSPEC ef(
					inboundMessages=0 and ex(inboundMessages>0 and raisedSignal(CONTENT_ERROR))
	)
	// eventualmente GEALAN passerà a recuperare da inbound. dopodichè, inbound sarà vuoto (pattern "After")
	CTLSPEC aw(
		not(ftpGEALAN=WITHDRAW_ORDER and state=NO_ORDER), 
		(ftpGEALAN=WITHDRAW_ORDER and state=NO_ORDER) and af(inboundMessages=0)
	)
	// gealan può inserire conferme in outbound eventualmente
	CTLSPEC ef(outboundMessages>0)
	// una volta che le conferme sono inserite, queste rimangono fino a quando il middleware non effettua un controllo. Tale controllo può essere fatto in qualsiasi momento in cui state=ORDER oppure ftpGEALAN!=CONFIRM_ORDER
	CTLSPEC absenceAfterUntil( 
		outboundMessages=0 , 
		(ftpGEALAN=CONFIRM_ORDER and outboundMessages>0) , 
		(state=ORDER or ftpGEALAN!=CONFIRM_ORDER)
	)
	// svuotare outboundMessages implica rendere non vuoto archivedMessages
	LTLSPEC g(
		(y(outboundMessages>0) and outboundMessages=0)
		implies
		(archivedOutboundMessages>0)
	)
	//-------------------------------------------------
	
	
	// MAIN RULE
	
	main rule r_mainWorkflow =
		if state=ORDER then
			par
				r_calculateErrors[]
				r_sendOrder[]
				r_checkConfirmation[]
			endpar
		else
			r_ftpInteraction[]
		endif
	
	//-------------------------------------------------

default init s0:

	function inboundMessages = 0
	function outboundMessages = 0
	function archivedOutboundMessages = 0
	
	function raisedSignal($s in Signal) = false