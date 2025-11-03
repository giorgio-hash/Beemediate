package com.beemediate.beemediate.domain.utils;

import org.jmlspecs.annotation.CodeBigintMath;
import org.jmlspecs.annotation.SkipEsc;

public class StringHandler {
	
	/*@ public normal_behaviour
	  @ requires s1==null || s2==null;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s1!=null & s1.length()==0;
	  @ requires s2!=null & s2.length()==0;
	  @ ensures \result;
	  @
	  @ also public normal_behaviour
	  @ requires s1!=null & s1.length()>=0;
	  @ requires s2!=null & s2.length()>=0;
	  @ requires s1.length()!=s2.length();
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s1!=null & s1.length()>0;
	  @ requires s2!=null & s2.length()>0;
	  @ requires s1.length()==s2.length();
	  @ ensures !\result <==> (\exists int i; 0<=i<s1.length(); s1.charAt(i) != s2.charAt(i));
	  @ ensures \result <==> (\forall int i; 0<=i<s1.length(); s1.charAt(i) == s2.charAt(i));
	  @*/
	@CodeBigintMath
	public /*@ pure @*/ static boolean equals(String s1, String s2) {
		
		if (s1==null || s2==null)
			return false;
		
		boolean sameSize = (s1.length() == s2.length());
		
		if(!sameSize) return false;
		
		if(s1.length() == 0)
			return true;
		
		boolean sameValue = true;
		
		int i=0;
		//@ loop_writes sameValue;
		//@ loop_invariant 0<=i<=s1.length();
		//@ loop_invariant !sameValue <==> (\exists int j; 0<=j<i; s1.charAt(j) != s2.charAt(j) );
		//@ decreases s1.length() - i;
		for(i=0; i<s1.length(); i++) {
		
			if(s1.charAt(i) != s2.charAt(i)) {
				//@ assert s1.charAt(i) != s2.charAt(i);
				sameValue = false;
				//@ assert !sameValue;
				break;
			}
			//@ assert s1.charAt(i) == s2.charAt(i);
		}
		
		return sameValue;
		
	}
	
	/*@ public normal_behaviour
	  @ requires str.length()==0;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()==1;
	  @ ensures \result <==> isDigit(str.charAt(0),false);
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>1;
	  @ requires (\exists int i; 0<=i<str.length(); !isDigit(str.charAt(i),false) );
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>1;
	  @ requires (\forall int i; 0<=i<str.length(); isDigit(str.charAt(i),false) );
	  @ ensures \result <==> isDigit(str.charAt(0),true);
	  @*/
	@CodeBigintMath
	public static /*@ helper pure @*/ boolean isInteger(/*@ non_null @*/ String str) {
		
		if(str == null || str.length()==0)
			return false;
		
		if(str.length() == 1) {
		
			return isDigit(str.charAt(0),false);
		
		}else {
			int i=0;
			//@ loop_writes \nothing;
			//@ maintaining 0<=i<=str.length();
			//@ maintaining i>0 ==> isDigit(str.charAt(0),true);
			//@ maintaining i>0 ==> (\forall int j; 1<=j<i; isDigit(str.charAt(j),false) );
			//@ decreases str.length()-i;
			for(; i<str.length(); i++) {
				
				if ( !isDigit( str.charAt(i), (i==0) ) )
					return false;
				
			}
		}
		
		return true;
	}
	
	
	//@ public static ghost int numOfCommas = 0;
	
	/*Pi� scenari:
	 * - scenario 1: stringa troppo corta --> false
	 * - scenario 2: stringa minima ma '.' agli estremi --> false
	 * - scenario 3: stringa minima, '.' nel mezzo ma c'� carattere sbagliato --> false
	 * - scenario 4: stringa minima, '.' non agli estremi, caratteri corretti e '.' al secondo posto --> true sse c'� solo un dot
	 * - scenario 5: stringa minima, '.' non agli estremi, caratteri corretti e '.' dopo il secondo posto --> true sse c'� solo un dot e primo carattere � non-nullo
	 * */
	/*@ public normal_behaviour
	  @ requires str.length()<3;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>=3;
	  @ requires str.charAt(str.length()-1) == '.' | str.charAt(0) == '.';
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>=3;
	  @ requires str.charAt(str.length()-1) != '.' & str.charAt(0) != '.';
	  @ requires (\exists int i; 0<=i<str.length(); (str.charAt(i)<48 | str.charAt(i)>57) & str.charAt(i)!='.');
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>=3;
	  @ requires str.charAt(str.length()-1) != '.' & str.charAt(0) != '.';
	  @ requires (\forall int i; 0<=i<str.length(); 48<=str.charAt(i)<=57 | str.charAt(i)=='.' );
	  @ requires str.charAt(1)=='.';
	  @ ensures \result <==> numOfCommas==1;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>=3;
	  @ requires str.charAt(str.length()-1) != '.' & str.charAt(0) != '.';
	  @ requires (\forall int i; 0<=i<str.length(); 48<=str.charAt(i)<=57 | str.charAt(i)=='.' );
	  @ requires str.charAt(1)!='.';
	  @ ensures \result <==> (numOfCommas==1 & str.charAt(0)!='0');
	  @*/
	@CodeBigintMath
	public static /*@ pure @*/ boolean isDouble(/*@ non_null @*/  String str) {
		
		final char COMMA = '.';
		int numOfCommas = 0;
		
		//@ set numOfCommas = 0;
		
		// voglio str: non null, forma minima '0.0', non forma troncata '0.', non forma troncata '.0' 
		if(str == null || str.length()<3 || str.charAt(str.length()-1) == COMMA || str.charAt(0) == COMMA)
			return false;
		
		// se il secondo carattere � COMMA, il primo carattere pu� essere zero.
		// in caso contrario, il primo carattere dev'essere diverso da zero.
		if ( str.charAt(1) != '.' & !isDigit(str.charAt(0),true) )
			return false;
		
		int i=0;
		//@ loop_writes numOfCommas;
		//@ maintaining 0<=numOfCommas<=str.length();
		//@ maintaining 0<=i<=str.length();
		//@ maintaining i>0 ==> (\forall int j; 0<=j<i; 48<=str.charAt(j)<=57 | str.charAt(j)=='.');
		//@ decreases str.length()-i;
		for(; i<str.length(); i++) {
				
			if( !isDigit(str.charAt(i),false) )
				if (str.charAt(i) == COMMA) {
					numOfCommas++;
					//@ set numOfCommas=numOfCommas+1;
				}else
					return false;
			
			}		
		
		return numOfCommas==1; // voglio solo un dot.
	}
	
	
	/*@ public normal_behaviour
	  @ requires c>=48 & c<=57;
	  @ requires nonNull == false;
	  @ ensures \result;
	  @
	  @ also public normal_behaviour
	  @ requires c>=48 & c<=57;
	  @ requires nonNull;
	  @ ensures \result <==> c!=48;
	  @
	  @ also public normal_behaviour
	  @ requires c<48 | c>57;
	  @ ensures !\result;
	  @*/
	public static /*@ pure @*/ boolean isDigit(char c, boolean nonNull) {
		
		if(nonNull)
			return 49<=c && c<=57;
		
		return 48<=c && c<=57;
	}
	
	/*@ public normal_behaviour
	  @ requires str.length()==0;
	  @ ensures \result == false;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()==1;
	  @ ensures \result <==> str.charAt(0)==elem;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()>1;
	  @ ensures \result <==> (\exists int i; 0<=i<str.length(); str.charAt(i)==elem);
	  @*/
	public static /*@ pure @*/ boolean containsChar( /*@ non_null @*/ String str, char elem) {
	
		if(str==null || str.length()==0)
			return false;
		
		/*@ loop_writes \nothing;
		  @ loop_invariant 0<=i<=str.length();
		  @ loop_invariant i>0 ==> (\forall int j; 0<=j<i; str.charAt(j)!=elem);
		  @ decreases str.length()-i;
		  @*/
		for(int i=0; i<str.length(); i++) {
			if(str.charAt(i)==elem)
				return true;
		}
		
		return false;
	}
	
	
	/*@ public normal_behaviour
	  @ requires str.length()!=19;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires str.length()==19;
	  @ requires (\exists int i; i==4 | i==7; str.charAt(i) != '-')
      @	  			| str.charAt(10) != 'T'
      @				| (\exists int i; i==13 | i==16; str.charAt(i) != ':');
      @ ensures !\result;
      @
      @ also public normal_behaviour
	  @ requires str.length()==19;
	  @ requires (\forall int i; i==4 | i==7; str.charAt(i) == '-')
      @	  			& str.charAt(10) == 'T'
      @				& (\forall int i; i==13 | i==16; str.charAt(i) == ':');
      @ ensures \result ==> isDigit(str.charAt(0),true);
      @ ensures \result ==> (\forall int i; 1<=i<str.length() & i!=4 & i!=7 & i!=10 & i!=13 & i!=16; isDigit(str.charAt(i),false) );
	  @*/
	public static /*@ pure @*/ boolean isDateTime(/*@ non_null @*/ String str) {
	
		// Guardo nello specifico il pattern "yyyy-MM-dd HH:mm:ss"
			
		final char MAIN_SEPARATOR = 'T';
		final char DATE_SEPARATOR = '-';
		final char TIME_SEPARATOR = ':';
		final int YSize = 4; 
		final int MSize = 2; 
		final int GSize = 2;
		final int hSize = 2; 
		final int mSize = 2; 
		final int sSize = 2;
		
		//mi aspetto una certa forma
		if( str.length() != YSize+MSize+GSize+hSize+mSize+sSize+5  )
			return false;
		
		//mi aspetto i separatori in determinate posizioni
		if(str.charAt(4)!=DATE_SEPARATOR
				|| str.charAt(7)!=DATE_SEPARATOR
				|| str.charAt(10)!=MAIN_SEPARATOR
				|| str.charAt(13)!=TIME_SEPARATOR
				|| str.charAt(16)!=TIME_SEPARATOR)
			return false;
		
		//controllo yyyy
		if( !isDigit(str.charAt(0), true) 
				|| !isDigit(str.charAt(1), false)  
				|| !isDigit(str.charAt(2), false)  
				|| !isDigit(str.charAt(3), false) )
			return false;
		
		final int MM=5;//MM index:controllo MM, da "01" a "12"
		final int dd=8;//dd index:controllo gg, da "01" a "31"
		final int HH=11;//HH index:controllo HH, da "00" a "23" 
		final int mm=14;//mm index:controllo mm, da "00" a "59"
		final int ss=17;//ss index:controllo ss, da "00" a "59"

		return (has2DigitsBetween(str, MM, '0','0','1','9') || has2DigitsBetween(str, MM, '1','1','0','2')) 
				&& (has2DigitsBetween(str, dd, '0','0','1','9') || has2DigitsBetween(str, dd, '1','2','0','9') || has2DigitsBetween(str, dd, '3','3','0','1'))
				&& (has2DigitsBetween(str, HH, '0','1','0','9') || has2DigitsBetween(str, HH, '2','2','0','3'))
				&& has2DigitsBetween(str, mm, '0','5','0','9') 
				&& has2DigitsBetween(str, ss, '0','5','0','9');
		
		}
	
	/*@
	  @ public normal_behaviour
	  @ requires s == null || s.length()==0;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s != null & s.length()>0;
	  @ requires index<0 || index>s.length() || index+1>s.length();
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s!=null & s.length()>0;
	  @ requires index>=0 & s.length()>index+1;
	  @ ensures \result ==> (isDigit(startRangeFirstDigit, false) & isDigit(endRangeFirstDigit, false)
        		& isDigit(startRangeSecondDigit, false) & isDigit(endRangeSecondDigit, false));
      @ ensures \result ==> (s.charAt(index) >= startRangeFirstDigit & s.charAt(index) <= endRangeFirstDigit &
        		s.charAt(index+1) >= startRangeSecondDigit & s.charAt(index+1) <= endRangeSecondDigit);
	  @*/
	@CodeBigintMath
    public static /*@ pure @*/ boolean has2DigitsBetween(String s, int index, 
    											char startRangeFirstDigit, char endRangeFirstDigit,
    											char startRangeSecondDigit, char endRangeSecondDigit) {
        if (s == null) return false;
        if (index < 0 || index + 1 >= s.length()) return false;
        if (!isDigit(startRangeFirstDigit, false) || !isDigit(endRangeFirstDigit, false)
        		|| !isDigit(startRangeSecondDigit, false) || !isDigit(endRangeSecondDigit, false) )
        				return false;
        
        char c1 = s.charAt(index);
        char c2 = s.charAt(index + 1);

        return c1 >= startRangeFirstDigit && c1 <= endRangeFirstDigit && 
        		c2 >= startRangeSecondDigit && c2 <= endRangeSecondDigit;
    }
	
	/*@ public normal_behaviour
	  @ requires date1!=null & date1.length()==19;
	  @ requires date2!=null & date2.length()==19;
	  @ requires !isDateTime(date1) | !isDateTime(date2);
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires date1!=null & date1.length()==19;
	  @ requires date2!=null & date2.length()==19;
	  @ requires isDateTime(date1) & isDateTime(date2);
	  @ ensures !\result<==> ((\exists int i; 0<=i<4; date1.charAt(i)>date2.charAt(i))
	  @							| (\exists int i; 5<=i<7; date1.charAt(i)>date2.charAt(i))
	  @							| (\exists int i; 8<=i<10; date1.charAt(i)>date2.charAt(i))
	  @							| (\exists int i; 11<=i<13; date1.charAt(i)>date2.charAt(i))
	  @							| (\exists int i; 14<=i<16; date1.charAt(i)>date2.charAt(i))
	  @							| (\exists int i; 17<=i<19; date1.charAt(i)>date2.charAt(i)));
	  @*/
	@CodeBigintMath
	public /*@ pure @*/ static boolean beforeOrEqualDateTime(/*@ non_null @*/String date1, /*@ non_null @*/String date2) {
		
		if(!isDateTime(date1) || !isDateTime(date2))
			return false;
		
		final int yyyy=0;//yyyy index
		final int MM=5;//MM index
		final int dd=8;//dd index
		final int HH=11;//HH index
		final int mm=14;//mm index
		final int ss=17;//ss index
		
		return (isSubstr1LessOrEqualThanSubstr2(date1,date2,yyyy,4)) &&
				(isSubstr1LessOrEqualThanSubstr2(date1,date2,MM,2)) &&
				(isSubstr1LessOrEqualThanSubstr2(date1,date2,dd,2)) &&
				(isSubstr1LessOrEqualThanSubstr2(date1,date2,HH,2)) &&
				(isSubstr1LessOrEqualThanSubstr2(date1,date2,mm,2)) &&
					(isSubstr1LessOrEqualThanSubstr2(date1,date2,ss,2));
	}

	/*@
	  @ public normal_behaviour
	  @ requires s1==null || s2==null || s1.length()==0 || s2.length()==0;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s1!=null & s1.length()>0;
	  @ requires s2!=null & s2.length()>0;
	  @ requires pos<0 || substrSize<=0;
	  @ ensures !\result;
	  @
	  @ also public normal_behaviour
	  @ requires s1!=null & s1.length()>0;
	  @ requires s2!=null & s2.length()>0;
	  @ requires pos>=0 & substrSize>0;
	  @ ensures !\result <==> ((\exists int j; pos<=j<pos+substrSize; s1.charAt(j)>s2.charAt(j) )
	  							| pos+substrSize>s1.length() 
	  							| pos+substrSize>s2.length());
	  @
	  @*/
	@CodeBigintMath
	public static /*@ pure @*/ boolean isSubstr1LessOrEqualThanSubstr2(String s1, String s2, int pos, int substrSize) {

		if(s1==null || s2==null || s1.length()==0 || s2.length()==0 ) return false;
		if(pos<0 || substrSize<=0) return false;
		if(pos+substrSize>s1.length() || pos+substrSize>s2.length()) return false;
		
		//@ loop_writes i;
		//@ loop_invariant 0<=i<=substrSize;
		//@ loop_invariant (\forall int j; pos<=j<pos+i; s1.charAt(j)<=s2.charAt(j) );
		//@ decreases substrSize-i;
		for(int i=0; i<substrSize; i++)
			if(s1.charAt(pos+i)>s2.charAt(pos+i))
				return false;
		
		return true;
	}
}
