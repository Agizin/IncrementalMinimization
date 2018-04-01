import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;


public class IncrementalNaive<P,S> extends IncrementalMinimization<P,S>
{

	private class EquivTestNaive extends EquivTest
	{
		
		public EquivTestNaive(DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
		}
		
		private Integer mintermTransition(Integer state, P minterm) throws TimeoutException
		{
			Integer toState = null;
			for (SFAInputMove<P,S> t : aut.getInputMovesFrom(state))
			{
				if (ba.IsSatisfiable(ba.MkAnd(minterm, t.guard)))
				{
					//aut is deterministic and complete. So, always one and exactly one transition per minterm.
					toState = t.to;
					break;
				}
			}
			assert(toState != null);
			return toState;
		}
		
		@Override
		public boolean isEquiv(Integer pStart, Integer qStart) throws TimeoutException
		{
			if (isKnownNotEqual(pStart,qStart))
			{
				return false;
			}
			EquivRecord start = new EquivRecord(pStart,qStart,path);
			Stack<EquivRecord> testStack = new Stack<EquivRecord>();
			testStack.add(start);
			while (!testStack.isEmpty())
			{
				EquivRecord curEquivTest = testStack.pop();
				Integer p = curEquivTest.pState;
				Integer q = curEquivTest.qState;
				HashSet<List<Integer>> curPath = curEquivTest.curPath;
				List<Integer> pair = normalize(p,q);
				HashSet<List<Integer>> newPath = new HashSet<List<Integer>>(curPath);
				newPath.add(pair);
				for (P minterm : minterms)
				{
					Integer pNextClass = equivClasses.find(mintermTransition(p, minterm));
					Integer qNextClass = equivClasses.find(mintermTransition(q, minterm));
					List<Integer> nextPair = normalize(pNextClass, qNextClass);
					if (!pNextClass.equals(qNextClass) && !equiv.contains(nextPair))
					{
						equiv.add(nextPair);
						if(isKnownNotEqual(pNextClass, qNextClass))
						{
							return false;
						}
						if(!newPath.contains(nextPair))
						{
							equiv.add(nextPair);
							EquivRecord nextTest = new EquivRecord(pNextClass, qNextClass, newPath);
							testStack.push(nextTest);
						}
					}
				}
			}
			equiv.add(normalize(pStart, qStart));
			return true;
		}
	}
	
	private final ArrayList<P> minterms;
	
	public IncrementalNaive(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		super(aut,ba);
		minterms = MintermTree.generate_minterms(aut, ba);
	}
	
	@Override
	protected EquivTest makeEquivTest(DisjointSets<Integer> equivClasses)
	{
		HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,0.9f);
		HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,0.9f);
		return new EquivTestNaive(equivClasses, equiv, path);
	}
}
