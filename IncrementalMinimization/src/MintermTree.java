import java.util.ArrayList;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;
import automata.sfa.SFAInputMove;

import theory.BooleanAlgebra;

public class MintermTree<P,S>
{
	public static <P,S> ArrayList<P> generate_minterms(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{	
		MintermTree<P,S> tree = new MintermTree<P,S>(ba, ba.True());
		for(SFAInputMove<P,S> p : aut.getInputMovesFrom(aut.getStates()))
		{
			tree.refine(p.guard);
		}
		return tree.getMinterms();
	}
	
	private final BooleanAlgebra<P,S> ba;
			
	private P root_pred;
	private MintermTree<P,S> left;
	private MintermTree<P,S> right;

	public MintermTree(BooleanAlgebra<P,S> ba, P root_pred)
	{
		this.ba = ba;
		this.root_pred = root_pred;
		left = null;
		right = null;
	}
			
	public boolean isLeaf()
	{
		return (left == null); //no single children are ever added, so this is a sufficient check
	}
			
	public void refine(P pred) throws TimeoutException
	{
		P predAnd = ba.MkAnd(root_pred, pred);
		P predAndNot = ba.MkAnd(root_pred, ba.MkNot(pred));
		if (ba.IsSatisfiable(predAnd) && ba.IsSatisfiable(predAndNot))
		{
			if (isLeaf())
			{
				this.left = new MintermTree<P,S>(ba, predAnd);
				this.right = new MintermTree<P,S>(ba, predAndNot);
			}
			else
			{
				left.refine(pred);
				right.refine(pred);
			}
		}
	}
	
	public ArrayList<P> getMinterms()
	{
		ArrayList<P> minterms = new ArrayList<P>();
		if (isLeaf())
		{
			minterms.add(root_pred);
		}
		else
		{
			minterms.addAll(left.getMinterms());
			minterms.addAll(right.getMinterms());
		}
		return minterms;
	}
}