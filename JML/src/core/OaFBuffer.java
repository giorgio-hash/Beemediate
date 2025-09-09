package core;

import org.jmlspecs.annotation.CodeBigintMath;

import core.DTO.Order;
import core.ports.entrypoint.NewOrdersEventIF;
import core.utils.BoundedBuffer;

public class OaFBuffer {
	
	private /*@ spec_public @*/ BoundedBuffer buffer;
	private /*@ spec_public @*/ OaFValidator validator;
	private /*@ spec_public @*/ NewOrdersEventIF or;
	
	/*@ public invariant buffer!=null; @*/
	/*@ public invariant 0<=buffer.ordini.length<=Integer.MAX_VALUE;  @*/
	/*@ public invariant validator!=null; @*/
	/*@ public invariant or!=null; @*/

	//@ requires bufferSize>0;
	//@ requires v != null;
	//@ requires orderRetriever != null;
	//@ ensures buffer != null;
	//@ ensures buffer.ordini.length>0;
	//@ ensures validator != null;
	//@ ensures or != null;
	//@ pure
	@CodeBigintMath
	public OaFBuffer(int bufferSize, /*@ non_null */OaFValidator v, /*@ non_null */ NewOrdersEventIF orderRetriever) {
		buffer = new BoundedBuffer(bufferSize);
		validator = v;
		or = orderRetriever;
	}

	/*@ normal_behaviour
	  @ assigns or.newOrder, buffer.ordini[*], buffer.size;
	  @ requires buffer != null;
	  @ requires or != null;
	  @ requires 0 < buffer.ordini.length <= Integer.MAX_VALUE;
	  @ requires 0 <= buffer.size <= buffer.ordini.length;
	  @ requires buffer.size>0 ==> (\forall int i; 0<=i<buffer.size; buffer.ordini[i]!=null);
	  @ requires buffer.size>0 ==> (\forall int i; 0<=i<buffer.size; buffer.ordini[i].data!=null);
	  @ requires buffer.size>0 ==> (\forall int i; 0<=i<buffer.size; buffer.ordini[i].quantity==null);
	  @ requires buffer.size<buffer.ordini.length ==> (\forall int i; buffer.size<=i<buffer.ordini.length; buffer.ordini[i]==null);
	  @ requires \elemtype(\typeof(buffer.ordini)) == \type(Order);
	  @ ensures 0<=\result<=buffer.ordini.length;
	  @ ensures \result == buffer.size;
	  @ diverges true;
	  @*/
	@CodeBigintMath
	public int loadNewOrders() {
		
		buffer.empty();
		
		if(or.fetchOrders()) { //c'è almeno un ordine
			Order t = or.popNewOrder();
			//@ loop_invariant 0<=buffer.size<=buffer.ordini.length;
			//@ loop_invariant buffer.size>0 ==> (\forall int i; 0<=i<buffer.size; buffer.ordini[i]!=null & buffer.ordini[i].data!=null & buffer.ordini[i].quantity!=null);
			//@ loop_invariant buffer.size<buffer.ordini.length ==> (\forall int i; buffer.size<=i<buffer.ordini.length; buffer.ordini[i]==null);
			//@ loop_invariant t!=null & t.data!=null & t.quantity!=null & \typeof(t) == \type(Order);
			do {
				if(!buffer.isFull())
					buffer.push(t);	
			}while( (t = or.popNewOrder())!=null && !buffer.isFull());
		}
		
		return buffer.size();
	}	
}
