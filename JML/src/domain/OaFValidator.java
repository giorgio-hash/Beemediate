package domain;

import DTO.QuantityFieldValue;
import DTO.Order;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;


public class OaFValidator {
	

	/*@ spec_public @*/ final String customerNumber = "3024005150";
	/*@ spec_public @*/ final QuantityFieldValue quantity = QuantityFieldValue.FLOAT_WITH_DOT;
	/*@ spec_public @*/ final char quantityMeasure = 'M';
	private /*@ spec_public @*/ final String[] deliveryLocationNumber = {"3024005150","30901505150"};
	private /*@ spec_public @*/ final String[] articleNumbers;


	//@ ensures articleNumbers != null;
	//@ ensures deliveryLocationNumber != null;
	//@ ensures quantityMeasure == 'M';
	//@ ensures quantity != null;
	//@ ensures customerNumber != null;
	public OaFValidator (/*@ non_null */String[] an) {
		articleNumbers = an;
	}
	
	//@ requires o != null;
	public void validate(/*@ non_null */Order o) {
		
	}
}
