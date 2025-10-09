package com.beemediate.beemediate.domain.utils;

//import org.jmlspecs.annotation.CodeBigintMath;

import com.beemediate.beemediate.domain.pojo.order.Order;

/**
 * Struttura dati per gestire un Array di Order utilizzando politica LIFO.
 */
public class BoundedBuffer {
	
	/***Array di elementi Order*/
	private final /*@ spec_public non_null @*/ Order[] ordini;
	/***numero di elementi Order attualmente inseriti in <tt>ordini</tt>*/
	private /*@ spec_public @*/ int size;
	
	
	/*@ public invariant 0 < ordini.length <= Integer.MAX_VALUE; @*/
	/*@ public invariant 0 <= size <= ordini.length; @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i]!=null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i].data!=null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i].quantity!=null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; ordini[i].orderID!=null); @*/
	/*@ public invariant size<ordini.length ==> (\forall int i; size<=i<ordini.length; ordini[i]==null); @*/
	/*@ public invariant size>0 ==> (\forall int i; 0<=i<size; \typeof(ordini[i])==\type(Order)); @*/
	/*@ public invariant \elemtype(\typeof(ordini)) == \type(Order); @*/
	
	/**
	 * Costruttore
	 * @param n - capacità dell'array <tt>ordini</tt>
	 */
	//@ public normal_behaviour
	//@ requires n>0;
	//@ ensures ordini != null;
	//@ ensures ordini.length == n;
	//@ ensures size == 0;
	//@ ensures (\forall int i; size<=i<ordini.length; ordini[i]==null);
	//@ pure
//	@CodeBigintMath
	public BoundedBuffer (final int n) {
		ordini = new Order[n];
		size = 0;
	}
	
	/**
	 * Restituisce elemento alla posizione <tt>i</tt>.
	 * @param i - int
	 * @return Order se <tt>i</tt> è un indice compreso tra 0 ed ordini.length-1 e ordini[i] esiste, altrimenti <i>null</i>;
	 */
	/*@ public normal_behaviour
	  @ assigns \nothing;
	  @ requires i>=0 & i<size;
	  @ ensures \result != null <==> (ordini[i]!=null & \result==ordini[i] & \typeof(\result) == \type(Order));
	  @ ensures \result == null <==> (i<0 | i>=size);
	  @ ensures size<ordini.length ==> (\forall int j; size<=j<ordini.length; ordini[j]==null);
	  @*/
//	@CodeBigintMath
	public /*@ pure nullable */ Order get(final int i) {
		if(0<=i && i<size)
			return ordini[i];
		return null;
	}

	/**
	 * Se il buffer non è pieno, inserisce un elemento nuovo.
	 * @param x - Order
	 */
	/*@ public normal_behaviour
	  @ assigns ordini[*], size;
	  @ requires x != null;
	  @ requires x.quantity!=null;
	  @ requires x.data!=null;
	  @ requires x.orderID!=null;
	  @ requires \typeof(x) == \type(Order);
	  @ ensures size == \old(size)+1 | size == \old(size);
	  @ ensures \old(size)<ordini.length <==> (size == \old(size)+1);
	  @ ensures size == \old(size)+1 ==> ordini[\old(size)] == x;
	  @ ensures size == \old(size)+1 ==> \typeof(ordini[\old(size)]) == \type(Order);
	  @*/
	public void push(final Order x) {
		if(size<ordini.length) {
			ordini[size] = x;
			size++;
		}
	}
	
	/**
	 * Se il buffer non è vuoto, restituisce un elemento Order.
	 * @return oggetto Order se buffer non vuoto, altrimenti <i>null</i>
	 */
	/*@ public normal_behaviour
	  @ assigns size, ordini[*];
	  @ requires ordini!=null & ordini.length>0 & size > 0;
	  @ requires \typeof(ordini[size-1]) == \type(Order);
	  @ ensures size == \old(size)-1;
	  @ ensures \result!=null & \typeof(\result) == \type(Order);
	  @ ensures size > 0 ==> \typeof(ordini[size-1]) == \type(Order);
	  @ also public normal_behaviour
	  @ assigns \nothing;
	  @ requires size==0;
	  @ ensures (size == \old(size));
	  @ ensures \result==null;
	  @*/

//	@CodeBigintMath
	public /*@ nullable */ Order pop() {
		/*@ nullable */ Order res=null;
		
		if(size>0) {
			size--;
			res = ordini[size]; 
			ordini[size] = null;
		} 
		return res;
	}
	
	/**
	 * Svuota il buffer.
	 */
	/*@ public normal_behaviour
	  @ assigns size, ordini[*];
	  @ ensures size == 0;
	  @ ensures (\forall int i; 0<=i<ordini.length; ordini[i]==null);
	  @*/
//	@CodeBigintMath
	public void empty() {

		//@ loop_invariant 0<=size<=ordini.length;
		//@ loop_invariant (\forall int i; size<=i<ordini.length; ordini[i]==null);
		while(size>0)
		{
			size--;
			ordini[size] = null;
		}
	}
	
	/**
	 * 
	 * @return int - numero di elementi attualmente nel buffer.
	 */
	/*@ public normal_behaviour
	  @ ensures \result == size;
	  @ ensures \not_modified(size);
	  @*/
	public /*@ pure @*/ int getSize() {
		return size;
	}
	
	/**
	 * 
	 * @return dimensione massima (capacità) del buffer.
	 */
	/*@ public normal_behaviour
	  @ ensures \result == ordini.length;
	  @*/
	public /*@ pure @*/ int capacity() {
		return ordini.length;
	}
	
	/**
	 * 
	 * @return <i>true</i> se il buffer è pieno.
	 */
	/*@ public normal_behaviour
	  @ ensures \result | size<ordini.length;
	  @*/
	public /*@ pure @*/ boolean isFull() {
		return ordini.length == size;
	}
	
	/**
	 * 
	 * @return <i>true</i> se il buffer è vuoto.
	 */
	/*@ public normal_behaviour
	  @ ensures \result | size>0;
	  @*/
	public /*@ pure @*/ boolean isEmpty() {
		return size==0;
	}

}