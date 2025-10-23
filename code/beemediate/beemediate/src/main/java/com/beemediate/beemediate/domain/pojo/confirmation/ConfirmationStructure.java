package com.beemediate.beemediate.domain.pojo.confirmation;

public class ConfirmationStructure {
	
	private String orderResponseDate;
	
	private String deliveryDate;
	
	private String orderId;
	
	private String orderIdGealan;
	
	private String addressName;

	private String addressStreet;

	private String addressZip;

	private String addressCity;

	private String addressCountry;

	private String addressCountryCoded;

	private int totalItemNum;
	
	private float totalAmount;
	
	private String currency;
	
	
	public ConfirmationStructure() {/*empty constructor*/}


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
	
	public void setOrderResponseDate(String orderResponseDate) {
		this.orderResponseDate =  orderResponseDate;
	}

	public void setDeliveryDate(String deliveryDate) {
		this.deliveryDate = deliveryDate;
	}

	public void setOrderId(String orderId) {
		this.orderId = orderId;
	}

	public void setOrderIdGealan(String orderIdGealan) {
		this.orderIdGealan = orderIdGealan;
	}

	public void setAddressName(String addressName) {
		this.addressName = addressName;
	}

	public void setAddressStreet(String addressStreet) {
		this.addressStreet = addressStreet;
	}

	public void setAddressZip(String addressZip) {
		this.addressZip = addressZip;
	}

	public void setAddressCity(String addressCity) {
		this.addressCity = addressCity;
	}

	public void setAddressCountry(String addressCountry) {
		this.addressCountry = addressCountry;
	}

	public void setAddressCountryCoded(String addressCountryCoded) {
		this.addressCountryCoded = addressCountryCoded;
	}

	public void setTotalItemNum(int totalItemNum) {
		this.totalItemNum = totalItemNum;
	}

	public void setTotalAmount(float totalAmount) {
		this.totalAmount = totalAmount;
	}

	public void setCurrency(String currency) {
		this.currency = currency;
	}

	public String getOrderResponseDate() {
		return orderResponseDate;
	}
	
	public String getDeliveryDate() {
		return deliveryDate;
	}

	public String getOrderId() {
		return orderId;
	}

	public String getOrderIdGealan() {
		return orderIdGealan;
	}

	public String getAddressName() {
		return addressName;
	}

	public String getAddressStreet() {
		return addressStreet;
	}

	public String getAddressZip() {
		return addressZip;
	}

	public String getAddressCity() {
		return addressCity;
	}

	public String getAddressCountry() {
		return addressCountry;
	}

	public String getAddressCountryCoded() {
		return addressCountryCoded;
	}
	
	public int getTotalItemNum() {
		return totalItemNum;
	}

	public float getTotalAmount() {
		return totalAmount;
	}
	
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
