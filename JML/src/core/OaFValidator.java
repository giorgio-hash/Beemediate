package core;

import core.DTO.QuantityFieldValue;
import core.DTO.Order;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class OaFValidator {
	

	/*@ spec_public @*/ final String customerNumber = "3024005150";
	/*@ spec_public @*/ final QuantityFieldValue quantity = QuantityFieldValue.FLOAT_WITH_DOT;
	/*@ spec_public @*/ final char quantityMeasure = 'M';
	private /*@ spec_public @*/ final String[] deliveryLocationNumber = {"3024005150","30901505150"};
	private /*@ spec_public @*/ String[] articleNumbers;


	/*@ normal_behaviour
	  @ ensures articleNumbers != null;
	  @ ensures deliveryLocationNumber != null;
	  @ ensures quantityMeasure == 'M';
	  @ ensures quantity != null;
	  @ ensures customerNumber != null;
	  @*/
	public OaFValidator () throws FileNotFoundException, IOException {
		String fileName = "./resources/Numero articolo GEALAN.txt";
		articleNumbers = readLines(fileName);
	}
	
	/*@ normal_behaviour
	  @ requires fileName != null;
	  @ ensures \result != null;
	  @*/
	private /*@ spec_public helper pure @*/ String[] readLines(String fileName) throws FileNotFoundException, IOException{
		FileReader fr;
		String[] rows = null;
		try {
			fr = new FileReader(fileName);
			BufferedReader br = new BufferedReader(fr);
			String row;
			String concatRows = "";
			if((row=br.readLine()) != null) {
				concatRows = row;
				while ((row=br.readLine()) != null) {
					concatRows += ";" + row;
				}
			}
					
			rows = concatRows.split(";");
		} catch (FileNotFoundException e0) {
			throw new FileNotFoundException();
		} catch (IOException e1) {
			throw new IOException();
		}
		return rows;
	}
	
	//@ requires o != null;
	public void validate(/*@ non_null */Order o) {
		
	}
}
