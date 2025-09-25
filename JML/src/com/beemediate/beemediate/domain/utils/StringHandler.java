package com.beemediate.beemediate.domain.utils;

import org.jmlspecs.annotation.CodeBigintMath;

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

}
