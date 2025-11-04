asm integrazione


import ../STDL/StandardLibrary
import ../STDL/CTLLibrary
import ../STDL/LTLLibrary

signature:

	//******************DOMINI PER IL SERVIZIO******************
	enum domain ServiceState = {NO_ORDER|ORDER|CONFIRMATION}
	enum domain GEALANOperation = {OFFLINE|WITHDRAW_ORDER|CONFIRM_ORDER}
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
							or hasQuantity(quantity) = FLOAT_WITH_COMMA
							or hasQuantity(quantity) = NAN
							
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
		
		
	//per reimpostare i segnali qualora non sono utilizzati
	rule r_resetSignals = forall $s in Signal do raisedSignal($s):=false	
	rule r_resetSignalsExcept($signal in Signal) = forall $s in Signal with $s!=$signal do raisedSignal($s):=false

		
	rule r_checkConfirmation =
		if outboundMessages>0 then
			seq
				archivedOutboundMessages := archivedOutboundMessages + outboundMessages
				outboundMessages := 0
				r_resetSignalsExcept[ODA_CONFIRMATION]
				raisedSignal(ODA_CONFIRMATION) := true
			endseq
		else
			par
				r_resetSignalsExcept[ODA_CONFIRMATION]
				raisedSignal(ODA_CONFIRMATION) := false
			endpar
		endif
	
	rule r_ftpInteraction =
			switch ftpGEALAN
				case WITHDRAW_ORDER :
					par
						r_resetSignals[]
						inboundMessages := 0
					endpar
				case CONFIRM_ORDER :
					par
						r_resetSignals[]
						outboundMessages := outboundMessages + 1
					endpar
				case OFFLINE :
						r_resetSignals[]
			endswitch
	
	//-------------------------------------------------
	
	
	// INVARIANTI
	// Se una conferma viene letta e poi archiviata, occrre saperlo
	invariant inv_archived over raisedSignal, archivedOutboundMessages : archivedOutboundMessages=0 implies not(raisedSignal(ODA_CONFIRMATION))
	// Il segnale di conferma OdA implica che le conferme sono state archiviate
	invariant inv_confirmed over raisedSignal, archivedOutboundMessages, outboundMessages : raisedSignal(ODA_CONFIRMATION) implies (outboundMessages=0 and archivedOutboundMessages>0)  
	//-------------------------------------------------
	
	
	// LTL/CTL
	// se c'è un'ordine e tutti i campi valutati sono ok, allora all'istante successivo ho per forza inbound>0
		LTLSPEC g( 
			(state=ORDER and checkOpenTransError=false and checkOpenTransError=false) 
			implies 
			( x(inboundMessages>0) )
	)
	// se ciò non accade, nell'istante successivo avrò signal(OPENTRANS_ERROR) oppure signal(CONTENT_ERROR) a seconda dei casi
			LTLSPEC g( 
			(state=ORDER and checkOpenTransError)
			implies 
			( x(raisedSignal(OPENTRANS_ERROR)))
	)
	
				CTLSPEC ag( 
			(state=ORDER and checkOpenTransError and inboundMessages=0)
			implies 
			ax( raisedSignal(OPENTRANS_ERROR) and inboundMessages=0 )
	)
	
				LTLSPEC g( 
			(state=ORDER and checkContentError)
			implies 
			( x(raisedSignal(CONTENT_ERROR)) )
	)
	
					CTLSPEC ag( 
			(state=ORDER and checkContentError and inboundMessages=0)
			implies 
			ex( (raisedSignal(CONTENT_ERROR)) and inboundMessages>=0)
	)
	// se inbound>0 allora resterà tale fino a che ftpGEALAN=WITHDRAW_ORDER
	CTLSPEC inboundMessages>0 implies au(inboundMessages>0, ftpGEALAN=WITHDRAW_ORDER)
	//quando ftpGEALAN=CONFIRM_ORDER allora dopo avrò che outbound>0
	LTLSPEC (state=NO_ORDER and ftpGEALAN=CONFIRM_ORDER)  implies x(outboundMessages>0)
	//se outbound>0 e CONFIRMATION allora nell'istante successivo avrò outbound=0 e archived>0 e signal(ODA_CONFIRMATION)
	LTLSPEC (outboundMessages=0 and raisedSignal(ODA_CONFIRMATION)) implies y(state=CONFIRMATION and outboundMessages>0)
	LTLSPEC (archivedOutboundMessages>0 and raisedSignal(ODA_CONFIRMATION)) implies y(state=CONFIRMATION and outboundMessages>0)
	//se archived>0 allora non tornerà mai archived=0
	CTLSPEC archivedOutboundMessages>0 implies af(archivedOutboundMessages>0)
	
	//-------------------------------------------------
	
	
	// MAIN RULE
	main rule r_mainWorkflow =
		switch state
			case ORDER:
				par
					r_calculateErrors[]
					r_sendOrder[]
				endpar
			case CONFIRMATION:
				r_checkConfirmation[]
			case NO_ORDER:
				r_ftpInteraction[]
		endswitch
	
	//-------------------------------------------------

default init s0:

	function inboundMessages = 0
	function outboundMessages = 0
	function archivedOutboundMessages = 0
	
	function raisedSignal($s in Signal) = false