package domain;

import org.jmlspecs.annotation.CodeBigintMath;

import DTO.Order;
import utils.BoundedBuffer;
import entrypoint.NewOrdersEventIF;

public class OaFBuffer {
	
	private /*@ spec_public @*/ BoundedBuffer buffer;
	private /*@ spec_public @*/ OaFValidator validator;
	private /*@ spec_public @*/ NewOrdersEventIF or;
	
	/*@ public invariant buffer!=null; @*/
	/*@ public invariant validator!=null; @*/
	/*@ public invariant or!=null; @*/
	
	//@ requires bufferSize>0;
	//@ requires v != null;
	//@ ensures buffer != null;
	//@ ensures validator != null;
	//@ pure
	public OaFBuffer(int bufferSize, /*@ non_null */OaFValidator v, /*@ non_null */ NewOrdersEventIF orderRetriever) {
		buffer = new BoundedBuffer(bufferSize);
		validator = v;
		or = orderRetriever;
	}


	//@ requires buffer != null & buffer.capacity()>0;
	//@ ensures 0<=buffer.size()<=buffer.capacity();
	@CodeBigintMath
	public void fetchNewOrders() {
		/*@ non_null*/Order[] neworders = or.fetchIncomingOrders();
		//@ assert neworders != null & (\forall int j; 0<=j<neworders.length; neworders[j] != null);
		//@ loop_writes buffer.elems[*], buffer.size;
		//@ loop_invariant neworders[i]!=null & buffer.size()>=0 & (\forall int y; 0<=y<i;buffer.get(buffer.size()-1-y)!=null & (\type(Order) == \typeof(buffer.get(buffer.size()-1-y))));
		//@ loop_invariant 0<=i<=neworders.length;
		for(int i=0; i<neworders.length; i=i+1) {
			buffer.push(neworders[i]);
			//@ assert \old(buffer).size()+1 == buffer.size();
		}
	}
	
}
