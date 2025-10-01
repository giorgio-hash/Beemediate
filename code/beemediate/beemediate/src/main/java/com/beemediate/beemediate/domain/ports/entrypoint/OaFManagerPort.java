package com.beemediate.beemediate.domain.ports.entrypoint;

public interface OaFManagerPort {
	
	public int handleConfirmations();
	
	public int handleOrders();

}
