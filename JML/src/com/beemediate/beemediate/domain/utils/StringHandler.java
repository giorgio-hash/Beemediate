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
	
	/*Più scenari:
	 * - scenario 1: stringa troppo corta --> false
	 * - scenario 2: stringa minima ma '.' agli estremi --> false
	 * - scenario 3: stringa minima, '.' nel mezzo ma c'è carattere sbagliato --> false
	 * - scenario 4: stringa minima, '.' non agli estremi, caratteri corretti e '.' al secondo posto --> true sse c'è solo un dot
	 * - scenario 5: stringa minima, '.' non agli estremi, caratteri corretti e '.' dopo il secondo posto --> true sse c'è solo un dot e primo carattere è non-nullo
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
		
		// se il secondo carattere è COMMA, il primo carattere può essere zero.
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
		char[] digits = new char[]{'0','1','2','3','4','5','6','7','8','9'};
		
		//@ loop_writes \nothing;
		//@ maintaining 0<=\count<=11;
		//@ loop_invariant (\forall int j; 0<=j<\count; c!=digits[j]);
		//@ decreases 10-\count;
		for(char digit : digits) {
			if(c == digit)
				return c=='0'? (nonNull? false : true) : true ;
		}
		return false;
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

}
