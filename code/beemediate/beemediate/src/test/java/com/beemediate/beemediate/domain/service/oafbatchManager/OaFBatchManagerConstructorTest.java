package com.beemediate.beemediate.domain.service.oafbatchManager;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import org.junit.Before;
import org.junit.Test;

import com.beemediate.beemediate.domain.exceptions.UnreachableThresholdException;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.ConfirmationProviderPort;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;
import com.beemediate.beemediate.domain.service.OaFBatchManager;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

public class OaFBatchManagerConstructorTest {

	private OaFBuffer oafMock;
	
	private BoundedBuffer buffer;	
	
	private ConfirmationProviderPort confirmationsMock;

	private FTPHandlerPort ftpMock;

	private DataSenderPort crmMock;
	
	@Before
	public void setup() {
		oafMock = mock(OaFBuffer.class);
		buffer = mock(BoundedBuffer.class);
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		confirmationsMock = mock(ConfirmationProviderPort.class);
		ftpMock = mock(FTPHandlerPort.class);
		crmMock = mock(DataSenderPort.class);
	}

	@Test
	public void testConstructor_whenThresholdAbove1() {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 0;
		
		assertThrows("Costruttore lancia eccezione (threshold<1)", IllegalArgumentException.class, ()->{
			OaFBatchManager oaf = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		});
	}
	
	@Test
	public void testConstructor_whenCapacity_belowThreshold() {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 2;
		
		assertThrows("Costruttore lancia eccezione (capacity<threshold --> non si raggiungerà mai soglia minima ordini)", UnreachableThresholdException.class, ()->{
			OaFBatchManager oaf = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		});
	}
	
	@Test
	public void testConstructor_whenCapacity_aboveThreshold() throws UnreachableThresholdException {
		
		when(buffer.capacity()).thenReturn(2);
		int threshold = 1;
		
		OaFBatchManager oafb = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		assertNotNull("Costruttore inizializzato correttamente", oafb );
	}
	
	@Test
	public void testConstructor_whenCapacity_equalsThreshold() throws UnreachableThresholdException {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 1;
		
		OaFBatchManager oafb = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		assertNotNull("Costruttore inizializzato correttamente", oafb );
	}
	
}
