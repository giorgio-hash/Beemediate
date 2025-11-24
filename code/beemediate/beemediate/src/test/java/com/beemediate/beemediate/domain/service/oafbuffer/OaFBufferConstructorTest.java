package com.beemediate.beemediate.domain.service.oafbuffer;

import static org.junit.Assert.assertNotNull;

import static org.junit.Assert.assertThrows;
import static org.mockito.Mockito.mock;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import com.beemediate.beemediate.domain.ports.infrastructure.odoo.OrderProviderPort;
import com.beemediate.beemediate.domain.service.OaFBuffer;
import com.beemediate.beemediate.domain.service.validator.OaFValidatorIF;

@RunWith(Parameterized.class)
public class OaFBufferConstructorTest {

	
	private int capacity;
	private OrderProviderPort orderProvMock;
	private OaFValidatorIF vMock;
	
	@Parameters
	public static Collection<Object[]> parameters() {
        return Arrays.asList(new Object[][]{
                {-1}, {0}, {5}
        });
    }
	
    public OaFBufferConstructorTest(int capacity) {
        this.capacity = capacity;
    }
    
    @Before
    public void setup() {
    	orderProvMock = mock(OrderProviderPort.class);
    	vMock = mock(OaFValidatorIF.class);
    }
    
    @Test
    public void test() {
    	
    	if(capacity>0)
    		assertNotNull("Oggetto creato corretttamente", new OaFBuffer(capacity, vMock , orderProvMock));
    	else {
    		assertThrows("Oggetto non creato, solleva eccezioni", Exception.class, ()->{
    			OaFBuffer oaf = new OaFBuffer(capacity, vMock , orderProvMock);
    		});
    	}
    }
}
