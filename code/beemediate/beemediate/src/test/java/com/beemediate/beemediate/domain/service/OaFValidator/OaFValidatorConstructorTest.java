package com.beemediate.beemediate.domain.service.OaFValidator;

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertThrows;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.when;

import java.lang.reflect.Field;
import java.util.Arrays;

import org.junit.Before;
import org.junit.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import com.beemediate.beemediate.domain.exceptions.EmptyArrayException;
import com.beemediate.beemediate.domain.ports.infrastructure.filesystem.SupplierCatalogReaderPort;
import com.beemediate.beemediate.domain.service.validator.impl.OaFValidator;

public class OaFValidatorConstructorTest {

		@Mock
		private SupplierCatalogReaderPort catalog;
		
		private OaFValidator ov;
		
		@Before
		public void setup(){
			MockitoAnnotations.openMocks(this);
		}
		
		@Test
		public void test_constructorwith_nullCatalog() {
			assertThrows(Exception.class, () -> {
				ov = new OaFValidator(null);
			});
		}
		
		@Test
		public void test_constructorwith_nullReadArticleNumbers() {
			when(catalog.readArticleNumbers()).thenReturn(null);
			assertThrows(EmptyArrayException.class, () -> {
				ov = new OaFValidator(catalog);
			});
		}
		
		@Test
		public void test_constructorwith_zeroReadArticleNumbers() {
			when(catalog.readArticleNumbers()).thenReturn(new String[0]);
			assertThrows(EmptyArrayException.class, () -> {
				ov = new OaFValidator(catalog);
			});
		}
		
		@Test
		public void test_constructorwith_manyArticleNumbers() throws EmptyArrayException, NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
			
			String[] sampleCatalog = new String[] {"aaa", "bbb", "ccc"};
			
			when(catalog.readArticleNumbers()).thenReturn(sampleCatalog);
			ov = new OaFValidator(catalog);
			
			assertNotNull("Oggetto istanziato", ov);
			
			//reflection per valutare attributo
			Field field = OaFValidator.class.getDeclaredField("articleNumbers");
	        field.setAccessible(true);
	        String[] actualCatalog = (String[]) field.get(ov);
	        
	        assertTrue("Catalogo inserito con successo", Arrays.deepEquals(sampleCatalog, actualCatalog));
		}
		
}
