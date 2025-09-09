package core.utils;

import org.jmlspecs.annotation.CodeBigintMath;
import core.DTO.Order;

public class BoundedBuffer {
	
	private final /*@ spec_public non_null @*/ Order[] ordini;
	private /*@ spec_public @*/ int size;
	
	
	/*@ public invariant 0 < ordini.length <= Integer.MAX_VALUE; @*/
	/*@ public invariant 0 <= size <= ordini.length; @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i]!=null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i].data!=null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i].quantity!=null); @*/
	/*@ public invariant size<ordini.length ==> (\forall int i; size<=i<ordini.length; ordini[i]==null); @*/
	/*@ public invariant \elemtype(\typeof(ordini)) == \type(Order); @*/
	
	//@ public normal_behaviour
	//@ requires n>0;
	//@ ensures ordini != null;
	//@ ensures ordini.length == n;
	//@ ensures size == 0;
	//@ pure
	public BoundedBuffer (int n) {
		ordini = new Order[n];
		size = 0;
	}
	
	/*@ public normal_behaviour
	  @ requires i>=0 & i<size;
	  @ ensures \result != null <==> ordini[i]!=null;
	  @ ensures \result == null <==> (i<0 | i>=size);
	  @*/
	@CodeBigintMath
	public /*@ pure nullable */ Order get(int i) {
		if(0<=i && i<size && size>0 && size<=ordini.length)
			return ordini[i];
		return null;
	}

	
	/*@ public normal_behaviour
	  @ assigns ordini[*], size;
	  @ requires x != null;
	  @ requires x.quantity!=null;
	  @ requires x.data!=null;
	  @ requires \typeof(x) == \type(Order);
	  @ ensures size == \old(size)+1 | size == \old(size);
	  @ ensures size == \old(size)+1 ==> ordini[\old(size)] == x;
	  @ ensures size == \old(size)+1 ==> \typeof(ordini[\old(size)]) == \type(Order);
	  @*/
	public void push(Order x) {
		if(size<ordini.length) {
			ordini[size] = x;
			size++;
		}
	}
	
	/*@ public normal_behaviour
	  @ assigns size, ordini[*];
	  @ requires size > 0 ==> \typeof(ordini[size-1]) == \type(Order);
	  @ ensures (size == \old(size)-1) | (size == \old(size));
	  @ ensures \result==null <==> (size == \old(size));
	  @ ensures \result!=null <==> (size == \old(size)-1) ;
	  @*/
	public /*@ nullable */ Order pop() {
		/*@ nullable */ Order res=null;
		
		if(size>0) {
			size--;
			res = ordini[size]; 
			ordini[size] = null;
		} 
		return res;
	}
	
	/*@ public normal_behaviour
	  @ assigns size, ordini[*];
	  @ ensures size == 0;
	  @ ensures (\forall int i; 0<=i<ordini.length; ordini[i]==null);
	  @*/
	@CodeBigintMath
	public void empty() {

		//@ loop_invariant 0<=size<=ordini.length;
		//@ loop_invariant (\forall int i; size<=i<ordini.length; ordini[i]==null);
		while(size>0)
		{
			size--;
			ordini[size] = null;
		}
	}
	
	/*@ public normal_behaviour
	  @ ensures \result == size;
	  @*/
	public /*@ pure @*/ int size() {
		return size;
	}
	
	/*@ public normal_behaviour
	  @ ensures \result == ordini.length;
	  @*/
	public /*@ pure @*/ int capacity() {
		return ordini.length;
	}
	
	/*@ public normal_behaviour
	  @ ensures \result | size<ordini.length;
	  @*/
	public /*@ pure @*/ boolean isFull() {
		return ordini.length == size;
	}

}