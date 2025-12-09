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

/**
 * Test class for the constructor of OaFBatchManager.
 * 
 * This class uses partition testing to validate the constructor behavior
 * by dividing input space into partitions and testing boundary conditions:
 * - Threshold below 1 (invalid partition)
 * - Capacity below threshold (invalid partition)
 * - Capacity above threshold (valid partition)
 * - Capacity equals threshold (boundary partition)
 */
public class OaFBatchManagerConstructorTest {

	/** Mock object for OaFBuffer dependency */
	private OaFBuffer oafMock;
	
	/** Mock object for BoundedBuffer dependency */
	private BoundedBuffer buffer;	
	
	/** Mock object for ConfirmationProviderPort dependency */
	private ConfirmationProviderPort confirmationsMock;

	/** Mock object for FTPHandlerPort dependency */
	private FTPHandlerPort ftpMock;

	/** Mock object for DataSenderPort dependency */
	private DataSenderPort crmMock;
	
	/**
	 * Setup method that initializes all mock objects before each test.
	 * Called before each test method execution.
	 */
	@Before
	public void setup() {
		oafMock = mock(OaFBuffer.class);
		buffer = mock(BoundedBuffer.class);
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		confirmationsMock = mock(ConfirmationProviderPort.class);
		ftpMock = mock(FTPHandlerPort.class);
		crmMock = mock(DataSenderPort.class);
	}

	/**
	 * Tests that the constructor throws IllegalArgumentException when threshold is below 1.
	 * Validates partition: invalid threshold values.
	 */
	@Test
	public void testConstructor_whenThresholdAbove1() {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 0;
		
		assertThrows("Costruttore lancia eccezione (threshold<1)", IllegalArgumentException.class, ()->{
			@SuppressWarnings("unused")
			OaFBatchManager oaf = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		});
	}
	
	/**
	 * Tests that the constructor throws UnreachableThresholdException when capacity is below threshold.
	 * Validates partition: capacity smaller than threshold (unreachable threshold).
	 */
	@Test
	public void testConstructor_whenCapacity_belowThreshold() {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 2;
		
		assertThrows("Costruttore lancia eccezione (capacity<threshold --> non si raggiungerà mai soglia minima ordini)", UnreachableThresholdException.class, ()->{
			@SuppressWarnings("unused")
			OaFBatchManager oaf = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		});
	}
	
	/**
	 * Tests that the constructor successfully initializes when capacity is above threshold.
	 * Validates partition: valid capacity and threshold relationship (capacity > threshold).
	 * 
	 * @throws UnreachableThresholdException if the threshold cannot be reached
	 */
	@Test
	public void testConstructor_whenCapacity_aboveThreshold() throws UnreachableThresholdException {
		
		when(buffer.capacity()).thenReturn(2);
		int threshold = 1;
		
		OaFBatchManager oafb = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		assertNotNull("Costruttore inizializzato correttamente", oafb );
	}
	
	/**
	 * Tests that the constructor successfully initializes when capacity equals threshold.
	 * Validates partition: boundary condition (capacity == threshold).
	 * 
	 * @throws UnreachableThresholdException if the threshold cannot be reached
	 */
	@Test
	public void testConstructor_whenCapacity_equalsThreshold() throws UnreachableThresholdException {
		
		when(buffer.capacity()).thenReturn(1);
		int threshold = 1;
		
		OaFBatchManager oafb = new OaFBatchManager(threshold, oafMock, confirmationsMock, ftpMock,  crmMock);
		assertNotNull("Costruttore inizializzato correttamente", oafb );
	}
	
}
