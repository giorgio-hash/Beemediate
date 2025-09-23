package domain.core;

import org.jmlspecs.annotation.CodeBigintMath;

import domain.core.dto.Order;
import domain.core.ports.entrypoint.NewOrdersEventIF;
import domain.core.utils.BoundedBuffer;

public class OaFBuffer {
	
	private /*@ spec_public @*/ final BoundedBuffer buffer;
	private /*@ spec_public @*/ final OaFValidatorIF validator;
	private /*@ spec_public @*/ final NewOrdersEventIF or;
	
	/*@ public invariant buffer!=null; @*/
	/*@ public invariant validator!=null; @*/
	/*@ public invariant or!=null; @*/

	//@ public normal_behaviour
	//@ requires bufferCapacity>0;
	//@ requires v != null;
	//@ requires orderRetriever != null;
	//@ ensures validator != null;
	//@ ensures or != null;
	//@ ensures buffer != null & buffer.ordini!=null;
	//@ ensures buffer.ordini.length==bufferCapacity & buffer.size==0;
	//@ ensures (\forall int i; buffer.size<=i<buffer.ordini.length; buffer.ordini[i]==null);
	//@ pure
	@CodeBigintMath
	public OaFBuffer(int bufferCapacity, OaFValidatorIF v, NewOrdersEventIF orderRetriever) {
		buffer = new BoundedBuffer(bufferCapacity);
		validator = v;
		or = orderRetriever;
	}

	/*@ public normal_behaviour
	  @ assigns or.newOrder, buffer.ordini[*], buffer.size;
	  @ requires buffer != null;
	  @ requires or != null;
	  @ ensures 0<=\result<=buffer.ordini.length;
	  @ ensures \result == buffer.size;
	  @ diverges true;
	  @*/
	@CodeBigintMath
	public int loadNewBuffer() {
		
		buffer.empty();
		//@ assert buffer.isEmpty();
		
		//@ ghost int ordersLoaded = 0;
		
		if(or.fetchOrders()) { //c'è almeno un ordine
			Order t = or.popNewOrder();
			//@ loop_writes buffer.ordini[*], t, ordersLoaded;
			//@ loop_invariant 0<=buffer.size<=buffer.ordini.length;
			/*@ loop_invariant 0<=ordersLoaded<=buffer.size;
			  @*/
			/*@ maintaining 0<buffer.size ==> (\forall int j; 0<=j<buffer.size; buffer.ordini[j] != null
			  @																		& buffer.ordini[j].data!=null 
			  @																		& buffer.ordini[j].quantity!=null
			  @																		& buffer.ordini[j].orderID!=null
			  @																		& \typeof(buffer.ordini[j]) == \type(Order));
			  @*/
			/*@ maintaining buffer.size<buffer.ordini.length ==> (\forall int j; buffer.size<=j<buffer.ordini.length; buffer.ordini[j]==null);
			  @*/
			//@ loop_invariant t!=null & t.data!=null & t.quantity!=null & t.orderID!=null & \typeof(t) == \type(Order);
			do {
				if(buffer.isFull())
					break;
				else{
					buffer.push(t);
					//@ assert ordersLoaded+1 == buffer.size;
					//@ set ordersLoaded = buffer.size;
				}
			}while( (t = or.popNewOrder())!=null);
		}
		
		//@ assert ordersLoaded == buffer.size;
		//@ assert buffer.size() == buffer.size;
		
		return buffer.size();
	}	
	
	/** Valida gli ordini presenti nel buffer (se presenti) e restituisce il numero di ordini idonei per l'invio.
	 * */
	/*@ public normal_behaviour
	  @ requires validator!=null;
	  @ requires buffer!=null & buffer.size>0 & buffer.size<=buffer.ordini.length;
	  @ requires buffer.size < buffer.ordini.length ==> (\forall int i; buffer.size<=i<buffer.ordini.length; buffer.ordini[i]==null);
	  @ requires 0<buffer.size ==> (\forall int i; 0<=i<buffer.size; buffer.ordini[i]!=null 
	  @																 & buffer.ordini[i].data!=null 
	  @																 & buffer.ordini[i].quantity!=null
	  @																 & buffer.ordini[i].orderID!=null
	  @																 & \typeof(buffer.ordini[i]) == \type(Order));
	  @ ensures \result>=0 & \result<=buffer.size;
	  @ ensures buffer.size>0 ==> (\forall int i; 0<=i<buffer.size; \old(buffer).ordini[i]==buffer.ordini[i]);
	  @ ensures \not_modified(buffer.size);
	  @ also public normal_behaviour
	  @ assigns \nothing;
	  @ requires buffer!=null & buffer.size==0;
	  @ ensures \result == 0;
	  @*/
	@CodeBigintMath
	public int validateBuffer() {
		int passed=0;
		
		//@ ghost int initialSize = buffer.size;
		
		if (buffer.size()>0) {
			
			//@ assert initialSize == buffer.size;
			
			/*@ nullable @*/Order o = null;
			
			//@ loop_writes buffer.ordini[*];
			//@ maintaining buffer.size == initialSize;
			//@ maintaining 0<=i<=initialSize;
			/*@ maintaining o!=null ==> o.data!=null 
			  @							& o.quantity!=null
			  @							& o.orderID!=null
			  @							& \typeof(o) == \type(Order);
			  @*/
			/*@ maintaining 0<buffer.size ==> (\forall int j; 0<=j<buffer.size; buffer.ordini[j] != null
			  @																		& buffer.ordini[j].data!=null 
			  @																		& buffer.ordini[j].quantity!=null
			  @																		& buffer.ordini[j].orderID!=null
			  @																		& \typeof(buffer.ordini[j]) == \type(Order));
			  @*/
			/*@ maintaining buffer.size<buffer.ordini.length ==> (\forall int j; buffer.size<=j<buffer.ordini.length; buffer.ordini[j]==null);
			  @*/
			//@ maintaining 0<=passed<=i & 0<=passed<=initialSize;
			//@ decreases buffer.size-i;
			for(int i=0;i<buffer.size();i++) {
				o = buffer.get(i);
				//@ assert \typeof(buffer.get(i)) == \typeof(o);
				//@ assert \typeof(buffer.get(i)) == \type(Order);
				//@ assert \typeof(o) == \type(Order);
				//@ assert initialSize == buffer.size;
				validator.validate(o);
				//@ assert o!=null;
				//@ assert initialSize == buffer.size;
				if (!o.hasOpenTransError())
					passed++;
			}
		}
		//@ assert passed<=buffer.size;
		//@ assert buffer.size == \old(buffer).size;
		return passed;
	}
	
	//@ public normal_behaviour
	//@ ensures \result == buffer;
	public /*@ pure @*/ BoundedBuffer getBuffer() {
		return buffer;
	}
}
