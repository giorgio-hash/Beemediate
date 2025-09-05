package domain;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class OaFBatchManager {

	public static void main(String[] args) {
		
		String[] articleNumbers = null;
		FileReader fr;
		try {
			fr = new FileReader("./resources/Numero articolo GEALAN.txt");
			BufferedReader br = new BufferedReader(fr);
			String row;
			String concatRows = "";
			if((row=br.readLine()) != null) {
				concatRows = row;
				while ((row=br.readLine()) != null) {
					concatRows += ";" + row;
				}
			}
			
			articleNumbers = concatRows.split(";");
		} catch (FileNotFoundException e0) {
			e0.printStackTrace();
		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e2) {
			e2.printStackTrace();
		}
		
		

	}

}
