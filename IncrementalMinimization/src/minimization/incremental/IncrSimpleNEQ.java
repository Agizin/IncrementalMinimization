package minimization.incremental;

import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import automata.sfa.SFA;

/*
 * CLASS FOR TESTING PURPOSES ONLY
 * 
 * This class uses a naive non-equivalence check that initially only checks
 * whether or not the given pair contains one final and one non-final state.
 */

public class IncrSimpleNEQ<P,S> extends IncrementalMinimization<P,S>
{
	protected class StateComparatorSimple extends StateComparator
	{
		@Override
		public int compare(Integer a, Integer b)
		{
			return a-b;
		}
	}

	public IncrSimpleNEQ(SFA<P, S> aut, BooleanAlgebra<P, S> ba) throws TimeoutException 
	{
		super(aut, ba);
		this.stateComp = new StateComparatorSimple();
		for(Integer p : aut.getFinalStates())
		{
			for(Integer q : aut.getNonFinalStates())
			{
				neq.add(normalize(p,q));
			}
		}
	}
	
	@Override
	protected LinkedHashMap<Integer, Integer> generateDistanceToFinalMap()
	{
		return null;
	}
	
	@Override
	protected Integer getStateDistanceToFinal(Integer state)
	{
		return 0;
	}
	
	@Override
	protected boolean isKnownNotEqual(Integer p, Integer q)
	{
		List<Integer> normalizedPair = normalize(p,q);
		return neq.contains(normalizedPair);
	}
}
