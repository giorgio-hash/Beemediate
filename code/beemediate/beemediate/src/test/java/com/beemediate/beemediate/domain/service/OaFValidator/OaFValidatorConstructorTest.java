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

/**
 * Unit test class for the {@link OaFValidator} constructor.
 * 
 * <p>This test class validates the initialization behavior of the OaFValidator class,
 * focusing on constructor parameter validation and state initialization. The tests ensure
 * that the OaFValidator properly handles edge cases and correctly initializes internal state
 * through the {@link SupplierCatalogReaderPort} dependency.
 * </p>
 * 
 * <p><b>Testing Approach:</b> This class employs unit testing methodologies with Mockito
 * to isolate the OaFValidator constructor from external dependencies. Mock objects are used
 * to simulate catalog behavior, allowing precise validation of constructor logic without
 * requiring actual implementations of the catalog port.
 * </p>
 * 
 * @see OaFValidator
 * @see SupplierCatalogReaderPort
 * @see EmptyArrayException
 */
public class OaFValidatorConstructorTest {

	/**
	 * Mocked instance of {@link SupplierCatalogReaderPort} used to simulate
	 * article catalog data retrieval.
	 */
	@Mock
	private SupplierCatalogReaderPort catalog;
	
	/**
	 * Instance of {@link OaFValidator} under test.
	 */
	private OaFValidator ov;
	
	/**
	 * Initializes Mockito annotations before each test execution.
	 */
	@Before
	public void setup(){
		MockitoAnnotations.openMocks(this);
	}
		
	/**
	 * Verifies that the OaFValidator constructor throws an exception
	 * when a null catalog is provided.
	 */
		@Test
		public void test_constructorwith_nullCatalog() {
			assertThrows(Exception.class, () -> {
				ov = new OaFValidator(null);
			});
		}
		
		
		/**
		 * Verifies that the OaFValidator constructor throws an {@link EmptyArrayException}
		 * when the catalog's readArticleNumbers() method returns null.
		 */
		@Test
		public void test_constructorwith_nullReadArticleNumbers() {
			when(catalog.readArticleNumbers()).thenReturn(null);
			assertThrows(EmptyArrayException.class, () -> {
				ov = new OaFValidator(catalog);
			});
		}
		
		/**
		 * Verifies that the OaFValidator constructor throws an {@link EmptyArrayException}
		 * when the catalog's readArticleNumbers() method returns an empty array.
		 */
		@Test
		public void test_constructorwith_zeroReadArticleNumbers() {
			when(catalog.readArticleNumbers()).thenReturn(new String[0]);
			assertThrows(EmptyArrayException.class, () -> {
				ov = new OaFValidator(catalog);
			});
		}
		
		/**
		 * Verifies that the OaFValidator constructor correctly initializes the internal
		 * articleNumbers field when provided with a valid non-empty catalog. Uses Java reflection
		 * to validate that the constructor properly stores the article numbers array.
		 * 
		 * @throws EmptyArrayException if the catalog is empty
		 * @throws NoSuchFieldException if the articleNumbers field does not exist
		 * @throws SecurityException if access to the field is denied
		 * @throws IllegalArgumentException if the field access argument is invalid
		 * @throws IllegalAccessException if the field cannot be accessed
		 */
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
