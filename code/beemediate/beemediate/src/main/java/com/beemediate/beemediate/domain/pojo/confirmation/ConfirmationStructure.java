package com.beemediate.beemediate.domain.pojo.confirmation;

/**
 * Rappresenta la struttura dati di una conferma d'ordine.
 * <p>
 * Questa classe è un semplice POJO che contiene i campi tipici di una
 * conferma d'ordine: date, identificativi, dati di indirizzo, numero totale
 * di articoli, importo totale e valuta. Fornisce un costruttore vuoto, un
 * costruttore di copia, metodi getter e setter per tutti i campi e una
 * implementazione di toString() che restituisce una rappresentazione testuale
 * dei principali campi.
 * </p>
 * <p>
 * Nota: i campi data sono trattati come Stringhe (il formato non è imposto da
 * questa classe). La gestione della validazione e del parsing delle date,
 * così come la sincronizzazione/immutabilità, sono responsabilità del codice
 * client che usa questa struttura.
 * </p>
 */
public class ConfirmationStructure {
	
	
	/**
	 * Data/ora di risposta dell'ordine (es. quando il sistema ha confermato l'ordine).
	 */
	private /*@ spec_public @*/ String orderResponseDate;
	
	/**
	 * Data prevista di consegna dell'ordine.
	 */
	private /*@ spec_public @*/ String deliveryDate;
	
	/**
	 * Identificativo dell'ordine (interno al sistema che invia/gestisce la conferma).
	 */
	private /*@ spec_public @*/ String orderId;
	
	/**
	 * Identificativo dell'ordine usato da Gealan (o altro sistema esterno).
	 */
	private /*@ spec_public @*/ String orderIdGealan;
	
	/**
	 * Nome del destinatario o ragione sociale associata all'indirizzo di consegna.
	 */
	private /*@ spec_public @*/ String addressName;

	/**
	 * Via/strada dell'indirizzo di consegna.
	 */
	private /*@ spec_public @*/ String addressStreet;

	/**
	 * CAP / codice postale dell'indirizzo di consegna.
	 */
	private /*@ spec_public @*/ String addressZip;

	/**
	 * Città dell'indirizzo di consegna.
	 */
	private /*@ spec_public @*/ String addressCity;

	/**
	 * Paese dell'indirizzo di consegna (nome completo).
	 */
	private /*@ spec_public @*/ String addressCountry;

	/**
	 * Paese dell'indirizzo di consegna in forma codificata (es. codice ISO).
	 */
	private /*@ spec_public @*/ String addressCountryCoded;

	/**
	 * Numero totale di articoli nell'ordine.
	 */
	private /*@ spec_public @*/ int totalItemNum;
	
	/**
	 * Importo totale dell'ordine.
	 */
	private /*@ spec_public @*/ float totalAmount;
	
	/**
	 * Valuta dell'importo totale (es. "EUR", "USD").
	 */
	private /*@ spec_public @*/ String currency;
	
	
	/**
	 * Costruttore vuoto.
	 */
	//@SkipEsc
	public ConfirmationStructure() {/*empty constructor*/}

	/**
	 * Costruttore di copia.
	 * Crea una nuova istanza copiando tutti i valori dall'istanza fornita.
	 * 
	 * @param copy l'istanza da cui copiare i dati; se nullo, il comportamento dipende dall'utilizzo successivo
	 */
	/*@ 
	  @ requires copy != null;
	  @ ensures this.orderResponseDate == copy.orderResponseDate;
	  @ ensures this.deliveryDate == copy.deliveryDate;
	  @ ensures this.orderId == copy.orderId;
	  @ ensures this.orderIdGealan == copy.orderIdGealan;
	  @ ensures this.addressName == copy.addressName;
	  @ ensures this.addressStreet == copy.addressStreet;
	  @ ensures this.addressZip == copy.addressZip;
	  @ ensures this.addressCity == copy.addressCity;
	  @ ensures this.addressCountry == copy.addressCountry;
	  @ ensures this.addressCountryCoded == copy.addressCountryCoded;
	  @ ensures this.totalItemNum == copy.totalItemNum;
	  @ ensures this.totalAmount == copy.totalAmount;
	  @ ensures this.currency == copy.currency;
	@*/
	public ConfirmationStructure(ConfirmationStructure copy) {
		super();
		this.orderResponseDate =  copy.orderResponseDate;
		this.deliveryDate = copy.deliveryDate;
		this.orderId = copy.orderId;
		this.orderIdGealan = copy.orderIdGealan;
		this.addressName = copy.addressName;
		this.addressStreet = copy.addressStreet;
		this.addressZip = copy.addressZip;
		this.addressCity = copy.addressCity;
		this.addressCountry = copy.addressCountry;
		this.addressCountryCoded = copy.addressCountryCoded;
		this.totalItemNum = copy.totalItemNum;
		this.totalAmount = copy.totalAmount;
		this.currency = copy.currency;
	}
	
	/**
	 * Imposta la data/ora di risposta dell'ordine.
	 * 
	 * @param orderResponseDate la data/ora di risposta (formato stringa)
	 */
	/*@ ensures this.orderResponseDate == orderResponseDate; @*/
	public void setOrderResponseDate(String orderResponseDate) {
		this.orderResponseDate =  orderResponseDate;
	}

	/**
	 * Imposta la data di consegna prevista.
	 * 
	 * @param deliveryDate la data di consegna (formato stringa)
	 */
	/*@ ensures this.deliveryDate == deliveryDate; @*/
	public void setDeliveryDate(String deliveryDate) {
		this.deliveryDate = deliveryDate;
	}

	/**
	 * Imposta l'identificativo dell'ordine.
	 * 
	 * @param orderId identificativo dell'ordine
	 */
	/*@ ensures this.orderId == orderId; @*/
	public void setOrderId(String orderId) {
		this.orderId = orderId;
	}

	/**
	 * Imposta l'identificativo dell'ordine nel sistema Gealan.
	 * 
	 * @param orderIdGealan identificativo Gealan
	 */
	/*@ ensures this.orderIdGealan == orderIdGealan; @*/
	public void setOrderIdGealan(String orderIdGealan) {
		this.orderIdGealan = orderIdGealan;
	}

	/**
	 * Imposta il nome associato all'indirizzo di consegna.
	 * 
	 * @param addressName nome o ragione sociale
	 */
	/*@ ensures this.addressName == addressName; @*/
	public void setAddressName(String addressName) {
		this.addressName = addressName;
	}

	/**
	 * Imposta la via/strada dell'indirizzo di consegna.
	 * 
	 * @param addressStreet la via/strada
	 */
	/*@ ensures this.addressStreet == addressStreet; @*/
	public void setAddressStreet(String addressStreet) {
		this.addressStreet = addressStreet;
	}

	/**
	 * Imposta il CAP / codice postale.
	 * 
	 * @param addressZip CAP / codice postale
	 */
	/*@ ensures this.addressZip == addressZip; @*/
	public void setAddressZip(String addressZip) {
		this.addressZip = addressZip;
	}

	/**
	 * Imposta la città dell'indirizzo di consegna.
	 * 
	 * @param addressCity la città
	 */
	/*@ ensures this.addressCity == addressCity; @*/
	public void setAddressCity(String addressCity) {
		this.addressCity = addressCity;
	}

	/**
	 * Imposta il paese dell'indirizzo di consegna (nome completo).
	 * 
	 * @param addressCountry nome del paese
	 */
	/*@ ensures this.addressCountry == addressCountry; @*/
	public void setAddressCountry(String addressCountry) {
		this.addressCountry = addressCountry;
	}

	/**
	 * Imposta il codice del paese dell'indirizzo di consegna (es. ISO).
	 * 
	 * @param addressCountryCoded codice paese
	 */
	/*@ ensures this.addressCountryCoded == addressCountryCoded; @*/
	public void setAddressCountryCoded(String addressCountryCoded) {
		this.addressCountryCoded = addressCountryCoded;
	}

	/**
	 * Imposta il numero totale di articoli nell'ordine.
	 * 
	 * @param totalItemNum numero totale di articoli
	 */
	/*@ ensures this.totalItemNum == totalItemNum; @*/
	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	/**
	 * Imposta l'importo totale dell'ordine.
	 * 
	 * @param totalAmount importo totale
	 */
	/*@ ensures this.totalAmount == totalAmount; @*/
	public void setTotalAmount(float totalAmount) {
		this.totalAmount = totalAmount;
	}

	/**
	 * Imposta la valuta dell'importo totale.
	 * 
	 * @param currency codice valuta (es. "EUR")
	 */
	/*@ ensures this.currency == currency; @*/
	public void setCurrency(String currency) {
		this.currency = currency;
	}

	/**
	 * Restituisce la data/ora di risposta dell'ordine.
	 * 
	 * @return la data/ora di risposta come stringa
	 */
	/*@ ensures \result == this.orderResponseDate; @*/
	public String getOrderResponseDate() {
		return orderResponseDate;
	}
	
	/**
	 * Restituisce la data di consegna prevista.
	 * 
	 * @return la data di consegna come stringa
	 */
	/*@ ensures \result == this.deliveryDate; @*/
	public String getDeliveryDate() {
		return deliveryDate;
	}

	/**
	 * Restituisce l'identificativo dell'ordine.
	 * 
	 * @return identificativo dell'ordine
	 */
	/*@ ensures \result == this.orderId; @*/
	public String getOrderId() {
		return orderId;
	}

	/**
	 * Restituisce l'identificativo dell'ordine nel sistema Gealan.
	 * 
	 * @return identificativo Gealan
	 */
	/*@ ensures \result == this.orderIdGealan; @*/
	public String getOrderIdGealan() {
		return orderIdGealan;
	}

	/**
	 * Restituisce il nome associato all'indirizzo di consegna.
	 * 
	 * @return nome o ragione sociale
	 */
	/*@ ensures \result == this.addressName; @*/
	public String getAddressName() {
		return addressName;
	}

	/**
	 * Restituisce la via/strada dell'indirizzo di consegna.
	 * 
	 * @return via/strada
	 */
	/*@ ensures \result == this.addressStreet; @*/
	public String getAddressStreet() {
		return addressStreet;
	}

	/**
	 * Restituisce il CAP / codice postale.
	 * 
	 * @return CAP / codice postale
	 */
	/*@ ensures \result == this.addressZip; @*/
	public String getAddressZip() {
		return addressZip;
	}

	/**
	 * Restituisce la città dell'indirizzo di consegna.
	 * 
	 * @return città
	 */
	/*@ ensures \result == this.addressCity; @*/
	public String getAddressCity() {
		return addressCity;
	}

	/**
	 * Restituisce il paese dell'indirizzo di consegna (nome completo).
	 * 
	 * @return nome del paese
	 */
	/*@ ensures \result == this.addressCountry; @*/
	public String getAddressCountry() {
		return addressCountry;
	}

	/**
	 * Restituisce il codice del paese dell'indirizzo di consegna (es. ISO).
	 * 
	 * @return codice paese
	 */
	/*@ ensures \result == this.addressCountryCoded; @*/
	public String getAddressCountryCoded() {
		return addressCountryCoded;
	}
	
	/**
	 * Restituisce il numero totale di articoli nell'ordine.
	 * 
	 * @return numero totale di articoli
	 */
	/*@ ensures \result == this.totalItemNum; @*/
	public int getTotalItemNum() {
		return totalItemNum;
	}

	/**
	 * Restituisce l'importo totale dell'ordine.
	 * 
	 * @return importo totale
	 */
	/*@ ensures \result == this.totalAmount; @*/
	public float getTotalAmount() {
		return totalAmount;
	}
	
	/**
	 * Restituisce la valuta dell'importo totale.
	 * 
	 * @return codice valuta
	 */
	/*@ ensures \result == this.currency; @*/
	public String getCurrency() {
		return currency;
	}


	@Override
	public String toString() {
		return "ConfirmationStructure [orderResponseDate="+orderResponseDate+"deliveryDate=" + deliveryDate + ", orderId=" + orderId + ", orderIdGealan="
				+ orderIdGealan + ", addressName=" + addressName + ", addressStreet=" + addressStreet + ", addressZip="
				+ addressZip + ", addressCity=" + addressCity + ", addressCountry=" + addressCountry
				+ ", addressCountryCoded=" + addressCountryCoded + ", totalItemNum=" + totalItemNum + ", totalAmount="
				+ totalAmount + ", currency=" + currency + "]";
	}
	
	
}
