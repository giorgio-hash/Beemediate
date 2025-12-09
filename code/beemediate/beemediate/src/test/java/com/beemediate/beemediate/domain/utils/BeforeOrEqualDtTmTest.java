package com.beemediate.beemediate.domain.utils;

import org.junit.Test;
import static org.junit.Assert.*;

/**
 * Testing su beforeOrEqualDateTime utilizzando 
 * <ul><li>PairWise Testing con algoritmo IPO</li>
 * <li>Statement Coverage per coprire casi extra</li>
 * </ul>
 */
public class StringHandlerBeforeOrEqualDateTimeTest {

/*
 * PairWise testing (algoritmo IPO)
 * Condizione: per ogni riga, massimo 1 LT ed 1 GT
 * 
CASE	yyyy      MM        dd        HH        mm        ss        data1        			   data2					isBeforeOrEqualDateTime
0		LT        EQ        GT        EQ        EQ        EQ        2024-11-15T18:28:54        2025-11-10T18:28:54		true
1		LT        GT        EQ        EQ        EQ        EQ        2024-12-18T18:28:54        2025-01-18T18:28:54		true
2		GT        LT        EQ        EQ        EQ        EQ        2026-05-10T18:28:54        2025-06-10T18:28:54		false
3		GT        EQ        LT        EQ        EQ        EQ        2026-11-05T18:28:54        2025-11-10T18:28:54		false
4		EQ        LT        GT        EQ        EQ        EQ        2025-05-20T18:28:54        2025-06-15T18:28:54		true
5		EQ        GT        LT        EQ        EQ        EQ        2025-12-05T18:28:54        2025-11-10T18:28:54		false
6		EQ        EQ        LT        GT        EQ        EQ        2025-11-10T20:28:54        2025-11-15T08:28:54		true
7		LT        EQ        EQ        GT        EQ        EQ        2024-11-18T20:28:54        2025-11-18T08:28:54		true
8		EQ        LT        EQ        GT        EQ        EQ        2025-05-18T20:28:54        2025-06-18T08:28:54		true
9		EQ        EQ        GT        LT        EQ        EQ        2025-11-20T06:28:54        2025-11-15T18:28:54		false
10		EQ        GT        EQ        LT        EQ        EQ        2025-12-18T06:28:54        2025-11-18T18:28:54		false
11		GT        EQ        EQ        LT        EQ        EQ        2026-11-18T06:28:54        2025-11-18T18:28:54		false
12		LT        EQ        EQ        EQ        GT        EQ        2024-11-18T18:45:54        2025-11-18T18:30:54		true
13		GT        EQ        EQ        EQ        LT        EQ        2026-11-18T18:15:54        2025-11-18T18:30:54		false
14		EQ        LT        EQ        EQ        GT        EQ        2025-05-18T18:45:54        2025-06-18T18:30:54		true
15		EQ        GT        EQ        EQ        LT        EQ        2025-12-18T18:15:54        2025-11-18T18:30:54		false
16		EQ        EQ        LT        EQ        GT        EQ        2025-11-10T18:45:54        2025-11-15T18:30:54		true
17		EQ        EQ        GT        EQ        LT        EQ        2025-11-20T18:15:54        2025-11-15T18:30:54		false
18		EQ        EQ        EQ        LT        GT        EQ        2025-11-18T06:45:54        2025-11-18T18:30:54		true
19		EQ        EQ        EQ        GT        LT        EQ        2025-11-18T20:15:54        2025-11-18T08:30:54		false
20		LT        EQ        EQ        EQ        EQ        GT        2024-11-18T18:28:55        2025-11-18T18:28:54		true
21		GT        EQ        EQ        EQ        EQ        LT        2026-11-18T18:28:53        2025-11-18T18:28:54		false
22		EQ        LT        EQ        EQ        EQ        GT        2025-05-18T18:28:55        2025-06-18T18:28:54		true
23		EQ        GT        EQ        EQ        EQ        LT        2025-12-18T18:28:53        2025-11-18T18:28:54		false
24		EQ        EQ        LT        EQ        EQ        GT        2025-11-10T18:28:55        2025-11-15T18:28:54		true
25		EQ        EQ        GT        EQ        EQ        LT        2025-11-20T18:28:53        2025-11-15T18:28:54		false
26		EQ        EQ        EQ        LT        EQ        GT        2025-11-18T06:28:55        2025-11-18T18:28:54		true
27		EQ        EQ        EQ        GT        EQ        LT        2025-11-18T20:28:53        2025-11-18T08:28:54		false
28		EQ        EQ        EQ        EQ        LT        GT        2025-11-18T18:15:55        2025-11-18T18:30:54		true
29		EQ        EQ        EQ        EQ        GT        LT        2025-11-18T18:45:53        2025-11-18T18:30:54		false
 * 
 * */
/*
 * in aggiunta (caso "equals")
30		EQ        EQ        EQ        EQ        EQ        EQ        2025-11-18T18:45:53        2025-11-18T18:45:53		true
 */
	

/**
  * PairWise testing (algoritmo IPO).
 * Condizione: per ogni riga, massimo 1 LT ed 1 GT.
 * * <p>
 * <table border="1">
 * <tr>
 * <th>CASE</th>
 * <th>yyyy</th>
 * <th>MM</th>
 * <th>dd</th>
 * <th>HH</th>
 * <th>mm</th>
 * <th>ss</th>
 * <th>data1</th>
 * <th>data2</th>
 * <th>isBeforeOrEqualDateTime</th>
 * </tr>
 * <tr>
 * <td>0</td> <td>LT</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2024-11-15T18:28:54</td> <td>2025-11-10T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>1</td> <td>LT</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2024-12-18T18:28:54</td> <td>2025-01-18T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>2</td> <td>GT</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2026-05-10T18:28:54</td> <td>2025-06-10T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>3</td> <td>GT</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2026-11-05T18:28:54</td> <td>2025-11-10T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>4</td> <td>EQ</td> <td>LT</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2025-05-20T18:28:54</td> <td>2025-06-15T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>5</td> <td>EQ</td> <td>GT</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>2025-12-05T18:28:54</td> <td>2025-11-10T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>6</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>2025-11-10T20:28:54</td> <td>2025-11-15T08:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>7</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>2024-11-18T20:28:54</td> <td>2025-11-18T08:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>8</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>2025-05-18T20:28:54</td> <td>2025-06-18T08:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>9</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>2025-11-20T06:28:54</td> <td>2025-11-15T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>10</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>2025-12-18T06:28:54</td> <td>2025-11-18T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>11</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>2026-11-18T06:28:54</td> <td>2025-11-18T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>12</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>2024-11-18T18:45:54</td> <td>2025-11-18T18:30:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>13</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>2026-11-18T18:15:54</td> <td>2025-11-18T18:30:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>14</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>2025-05-18T18:45:54</td> <td>2025-06-18T18:30:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>15</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>2025-12-18T18:15:54</td> <td>2025-11-18T18:30:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>16</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>2025-11-10T18:45:54</td> <td>2025-11-15T18:30:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>17</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>2025-11-20T18:15:54</td> <td>2025-11-15T18:30:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>18</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>GT</td> <td>EQ</td> <td>2025-11-18T06:45:54</td> <td>2025-11-18T18:30:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>19</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>LT</td> <td>EQ</td> <td>2025-11-18T20:15:54</td> <td>2025-11-18T08:30:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>20</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>2024-11-18T18:28:55</td> <td>2025-11-18T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>21</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>2026-11-18T18:28:53</td> <td>2025-11-18T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>22</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>2025-05-18T18:28:55</td> <td>2025-06-18T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>23</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>2025-12-18T18:28:53</td> <td>2025-11-18T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>24</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>2025-11-10T18:28:55</td> <td>2025-11-15T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>25</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>2025-11-20T18:28:53</td> <td>2025-11-15T18:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>26</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>EQ</td> <td>GT</td> <td>2025-11-18T06:28:55</td> <td>2025-11-18T18:28:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>27</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>EQ</td> <td>LT</td> <td>2025-11-18T20:28:53</td> <td>2025-11-18T08:28:54</td> <td>false</td>
 * </tr>
 * <tr>
 * <td>28</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>LT</td> <td>GT</td> <td>2025-11-18T18:15:55</td> <td>2025-11-18T18:30:54</td> <td>true</td>
 * </tr>
 * <tr>
 * <td>29</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>EQ</td> <td>GT</td> <td>LT</td> <td>2025-11-18T18:45:53</td> <td>2025-11-18T18:30:54</td> <td>false</td>
 * </tr>
 * </table>
 * </p>
 * <br><br>in aggiunta (caso "equals")
	<br>30		EQ        EQ        EQ        EQ        EQ        EQ        2025-11-18T18:45:53        2025-11-18T18:45:53		true
 */
	@Test
	public void test_pairWise() {
		//0		-->	2024-11-15T18:28:54        2025-11-10T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2024-11-15T18:28:54", "2025-11-10T18:28:54"));
		//1		-->	2024-12-18T18:28:54        2025-01-18T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2024-12-18T18:28:54", "2025-01-18T18:28:54"));
		//2		-->	2026-05-10T18:28:54        2025-06-10T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2026-05-10T18:28:54", "2025-06-10T18:28:54"));
		//3		-->	2026-11-05T18:28:54        2025-11-10T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2026-11-05T18:28:54", "2025-11-10T18:28:54"));
		//4		-->	2025-05-20T18:28:54        2025-06-15T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-05-20T18:28:54", "2025-06-15T18:28:54"));
		//5		-->	2025-12-05T18:28:54        2025-11-10T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-12-05T18:28:54", "2025-11-10T18:28:54"));
		//6 	-->	2025-11-10T20:28:54        2025-11-15T08:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-10T20:28:54", "2025-11-15T08:28:54"));
		//7		-->	2024-11-18T20:28:54        2025-11-18T08:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2024-11-18T20:28:54", "2025-11-18T08:28:54"));
		//8		-->	2025-05-18T20:28:54        2025-06-18T08:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-05-18T20:28:54", "2025-06-18T08:28:54"));
		//9		-->	2025-11-20T06:28:54        2025-11-15T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-20T06:28:54", "2025-11-15T18:28:54"));
		//10	-->	2025-12-18T06:28:54        2025-11-18T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-12-18T06:28:54", "2025-11-18T18:28:54"));
		//11	-->	2026-11-18T06:28:54        2025-11-18T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2026-11-18T06:28:54", "2025-11-18T18:28:54"));
		//12	-->	2024-11-18T18:45:54        2025-11-18T18:30:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2024-11-18T18:45:54", "2025-11-18T18:30:54"));
		//13	-->	2026-11-18T18:15:54        2025-11-18T18:30:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2026-11-18T18:15:54", "2025-11-18T18:30:54"));
		//14	-->	2025-05-18T18:45:54        2025-06-18T18:30:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-05-18T18:45:54", "2025-06-18T18:30:54"));
		//15	-->	2025-12-18T18:15:54        2025-11-18T18:30:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-12-18T18:15:54", "2025-11-18T18:30:54"));
		//16	-->	2025-11-10T18:45:54        2025-11-15T18:30:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-10T18:45:54", "2025-11-15T18:30:54"));
		//17	-->	2025-11-20T18:15:54        2025-11-15T18:30:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-20T18:15:54", "2025-11-15T18:30:54"));
		//18	-->	2025-11-18T06:45:54        2025-11-18T18:30:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-18T06:45:54", "2025-11-18T18:30:54"));
		//19	-->	2025-11-18T20:15:54        2025-11-18T08:30:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-18T20:15:54", "2025-11-18T08:30:54"));
		//20	-->	2024-11-18T18:28:55        2025-11-18T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2024-11-18T18:28:55", "2025-11-18T18:28:54"));
		//21	-->	2026-11-18T18:28:53        2025-11-18T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2026-11-18T18:28:53", "2025-11-18T18:28:54"));
		//22	-->	2025-05-18T18:28:55        2025-06-18T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-05-18T18:28:55", "2025-06-18T18:28:54"));
		//23	-->	2025-12-18T18:28:53        2025-11-18T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-12-18T18:28:53", "2025-11-18T18:28:54"));
		//24	-->	2025-11-10T18:28:55        2025-11-15T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-10T18:28:55", "2025-11-15T18:28:54"));
		//25	-->	2025-11-20T18:28:53        2025-11-15T18:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-20T18:28:53", "2025-11-15T18:28:54"));
		//26	-->	2025-11-18T06:28:55        2025-11-18T18:28:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-18T06:28:55", "2025-11-18T18:28:54"));
		//27	-->	2025-11-18T20:28:53        2025-11-18T08:28:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-18T20:28:53", "2025-11-18T08:28:54"));
		//28	-->	2025-11-18T18:15:55        2025-11-18T18:30:54		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-18T18:15:55", "2025-11-18T18:30:54"));
		//29	-->	2025-11-18T18:45:53        2025-11-18T18:30:54		false
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-18T18:45:53", "2025-11-18T18:30:54"));
		//30	-->	2025-11-18T18:45:53        2025-11-18T18:45:53		true
		assertTrue(StringHandler.beforeOrEqualDateTime("2025-11-18T18:45:53", "2025-11-18T18:45:53"));
	}
	
	/**
	 * caso supplementare per completare branch+statement coverage
	 *  */ 
	@Test
	public void test_allEquals_but_ss1GreaterThanss2() {
		assertFalse(StringHandler.beforeOrEqualDateTime("2025-11-18T18:45:53", "2025-11-18T18:45:52"));
	}
	
	
	/**
	 * branch+statement coverage della guardia iniziale
	 */
    @Test
    public void test_date1Null_date2Valid() {
        String date1 = null;
        String date2 = "2020-01-01T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }

	/**
	 * Statement Coverage supplementare
	 */
    @Test
    public void test_date1Valid_date2Null() {
        String date1 = "2020-01-01T00:00:00";
        String date2 = null;
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }
    
	/**
	 * Statement Coverage supplementare
	 */
    @Test
    public void test_date1Valid_date2Invalid() {
        String date1 = "2020-01-01T00:00:00";
        String date2 = "2020-01-T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }
    
	/**
	 * Statement Coverage supplementare
	 */
    @Test
    public void test_date1Invalid_date2Valid() {
    	String date1 = "2020-01-01T0000:00:00";
    	String date2 = "2020-01-01T00:00:00";
        assertFalse(StringHandler.beforeOrEqualDateTime(date1, date2));
    }
    
}