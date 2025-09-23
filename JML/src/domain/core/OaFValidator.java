package domain.core;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.jmlspecs.annotation.CodeBigintMath;

import domain.core.dto.Order;
import domain.core.dto.QuantityFieldValue;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class OaFValidator implements OaFValidatorIF{
	

	/*@ spec_public */ final String customerNumber = "3024005150";
	/*@ spec_public */ final QuantityFieldValue quantity = QuantityFieldValue.FLOAT_WITH_DOT;
	/*@ spec_public */ final char quantityMeasure = 'M';
	private /*@ spec_public */ final String[] deliveryLocationNumber = {"3024005150","30901505150"};
	private /*@ spec_public */ final String[] articleNumbers;
	

	/*@ public normal_behaviour
	  @ requires articlesID!=null & articlesID.length>0;
	  @ requires (\forall int i; 0<=i<articlesID.length;articlesID[i]!=null & articlesID[i].length()>0);
	  @ ensures customerNumber!=null;
	  @ ensures quantity != null;
	  @ ensures quantityMeasure == 'M';
	  @ ensures deliveryLocationNumber!=null & deliveryLocationNumber.length==2;
	  @ ensures articleNumbers!=null & articleNumbers.length>0;
	  @ diverges true;
	  @ also public exceptional_behaviour
	  @ requires articlesID!=null & articlesID.length>0 & (\exists int i; 0<=i<articlesID.length;articlesID[i]==null | articlesID[i].length()==0);
	  @ signals_only Exception;
	  @ diverges true;
	  @ also public exceptional_behaviour
	  @ requires articlesID==null;
	  @ signals_only Exception;
	  @*/
	@CodeBigintMath
	public /*@ pure*/ OaFValidator (String[] articlesID) throws Exception {
		if (articlesID == null) throw new Exception("No dati per numero articoli");
	    //@ maintaining 0 <= \count <= articlesID.length;
	    //@ maintaining (\forall int k; 0 <= k < \count; articlesID[k] != null & articlesID[k].length()!=0);
	    //@ loop_writes \nothing;
	    //@ decreases articlesID.length - \count;
		for(String str : articlesID) {
			if(str == null || str.isEmpty())
				throw new Exception("Articolo con identificativo vuoto");
		}
		articleNumbers = articlesID;
		//"./resources/Numero articolo GEALAN.txt"
	}
	

	@Override
	public void validate(Order o) {
		// TODO Auto-generated method stub
		
	}

}
