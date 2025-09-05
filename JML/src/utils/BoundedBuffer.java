package utils;

import org.jmlspecs.annotation.CodeBigintMath;

import DTO.Order;

public class BoundedBuffer { 
    private /*@ spec_public non_null @*/ Order[] elems; 
    private /*@ spec_public non_null @*/ int size = 0; 
  
    //@ public invariant elems.length > 0;
    //@ public invariant size >=0; 
    //@ public invariant (\forall int i; i>= 0 && i < size; elems[i] != null); 
    //@ public invariant (\forall int i; i>= size && i < elems.length; elems[i] == null); 
    //@ public invariant \typeof(elems) == \type(Order[]);  
    
    //@ requires n > 0; 
    //@ ensures elems.length == n;
    //@ pure
    @CodeBigintMath
    public BoundedBuffer(int n) { 
        elems = new Order[n];
    } 
  
    // pre: ogni elemento dell'array ha tipo dinamico Order 
    // post: size viene incrementato e l'oggetto viene inserito correttamente, lasciando inalterato il buffer
    // https://github.com/OpenJML/OpenJML/issues/628
    //@ requires \type(Order) <: \elemtype(\typeof(elems));
    //@ requires 0<=size & size < elems.length; 
    //@ requires x != null;
    //@ requires \typeof(x) == \type(Order);
    //@ ensures size == \old(size) +1;
    //@ ensures elems[\old(size)] != null & ( \type(Order) <: \typeof(elems[\old(size)]));
    //@ ensures (\forall int i; 0<=i & i<elems.length & i != \old(size); \old(elems[i]) == elems[i]);
    public void push( /*@ non_null @*/ Order x) { 
    	if(size < elems.length) {
    		elems[size] = x;
	        size++; 	
    	}
    } 
  
    // pre: non è vuoto 
    // post size decrementato, oggetto tolto (ma gli altri rimangono uguali) 
    //@ requires 0<size<=elems.length;    
    //@ ensures size == \old(size) -1; 
    //@ ensures (\forall int i; i>= 0 && i < elems.length && i != size; elems[i] == \old(elems[i])); 
    //@ ensures elems[size] == null; 
    public void pop() { 
        size--; 
        elems[size] = null; 
    } 
	
    // pre: non è vuoto, l'indice in input è entro i confini
    // post: elemento è restituito solo se i è entro i confini
    //@ requires 0<=size<elems.length;
    //@ requires 0<=i<size;
    //@ ensures \result != null;
    @CodeBigintMath
    public /*@ pure @*/ Order get(int i) {
    	return elems[i];
    }
    
	// pre: non è vuoto 
    // restituisce l'ultimo oggetto 
    //@ requires elems.length>0;
    //@ requires 0<size<=elems.length;
	//@ ensures \result==elems[size-1];
    @CodeBigintMath
	public /*@ pure @*/ Order top() {
		return elems[size - 1];
	}
     
    //@ ensures \result == size;
    public /*@ pure @*/ int size() {
    	return size;
    }
    
    //@ ensures \result >= 0;
    public /*@ pure @*/ int capacity() {
    	return elems.length;
    }

}
