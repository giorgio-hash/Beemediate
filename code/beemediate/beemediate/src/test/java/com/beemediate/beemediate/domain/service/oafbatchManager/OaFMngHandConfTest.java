package com.beemediate.beemediate.domain.service.oafbatchManager;

import static org.junit.Assert.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import java.util.Stack;

import org.junit.Before;
import org.junit.Test;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;

import com.beemediate.beemediate.domain.exceptions.UnreachableThresholdException;
import com.beemediate.beemediate.domain.pojo.confirmation.Confirmation;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.ConfirmationProviderPort;
import com.beemediate.beemediate.domain.ports.infrastructure.ftp.FTPHandlerPort;
import com.beemediate.beemediate.domain.ports.infrastructure.odoo.DataSenderPort;
import com.beemediate.beemediate.domain.service.OaFBatchManager;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.utils.BoundedBuffer;

/**
 * 
 * test per verificare gestione conferme.
 * - implementazione scenario checkConfirmation.avalla
 */
public class OaFMngHandConfTest {

	private OaFBuffer oafMock;
	
	private BoundedBuffer buffer;	
	
	private ConfirmationProviderPort confirmationsMock;

	private FTPHandlerPort ftpMock;

	private DataSenderPort crmMock;
	
	private OaFBatchManager oafb;
	
	private Stack<Confirmation> cStackMock;
	
	private int archived;
	private int confirmed;
	
	
	@Before
	public void setup() throws UnreachableThresholdException{
		
		archived=0;
		confirmed=0;
		
		oafMock = mock(OaFBuffer.class);
		confirmationsMock = mock(ConfirmationProviderPort.class);
		ftpMock = mock(FTPHandlerPort.class);
		crmMock = mock(DataSenderPort.class);
		
		when(ftpMock.archive(any(Confirmation.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				archived += 1;
				return true;
			}
		});
		when(crmMock.signalConfirmation(any(Confirmation.class))).then(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				
				confirmed += 1;
				return true;
			}
		});
		
		cStackMock = new Stack<>();
		Confirmation c = new Confirmation("esempio1", null);cStackMock.add(c);

		when(confirmationsMock.hasConfirmation()).thenAnswer(new Answer<Boolean>() {
			@Override
			public Boolean answer(InvocationOnMock invocation) throws Throwable {
				
				return !cStackMock.isEmpty();
			}
		});
		when(confirmationsMock.popConfirmation()).thenAnswer(new Answer<Confirmation>() {
			@Override
			public Confirmation answer(InvocationOnMock invocation) throws Throwable {
				
				return cStackMock.isEmpty()? null : cStackMock.pop();
			}
		});
		
		
		buffer = new BoundedBuffer(1);
		when(oafMock.loadNewBuffer()).thenReturn(buffer.getSize());
		when(oafMock.getBuffer()).thenReturn(buffer);
		
		oafb = new OaFBatchManager(1, oafMock, confirmationsMock, ftpMock,  crmMock);
	}
	
	//---------------------------------------------Scenario checkConfirmation.avalla
	
	@Test
	public void test_checkConfirmation_state0() {
		
		when(confirmationsMock.fetchConfirmations()).thenReturn(false);
		
		int result = oafb.handleConfirmations();
		
		assertEquals("Nessuna conferma è stata effettivamente processata", 0, result);
		assertEquals("Nessuna conferma è stata archiviata", 0, archived);
		assertEquals("Nessun segnale di conferma", 0, confirmed);
	} 
	
	@Test
	public void test_checkConfirmation_state2() {
		
		when(confirmationsMock.fetchConfirmations()).thenReturn(true);
		
		int result = oafb.handleConfirmations();
		
		assertEquals("conferma effettivamente processata", 1, result);
		assertEquals("conferma è stata archiviata", 1, archived);
		assertEquals("segnale di conferma", 1, confirmed);
	} 
	
	
	//---------------------------------------------------fuori modello: caso multi-conferma
	@Test
	public void test_checkConfirmation_state2_multiConfirmation() {
		
		when(confirmationsMock.fetchConfirmations()).thenReturn(true);
		Confirmation c1 = new Confirmation("esempio2", null);cStackMock.add(c1);
		
		int result = oafb.handleConfirmations();
		
		assertEquals("conferma effettivamente processata", 2, result);
		assertEquals("conferma è stata archiviata", 2, archived);
		assertEquals("segnale di conferma", 2, confirmed);
	} 
}
