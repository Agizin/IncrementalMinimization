import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;


public class MooreMinimization
{
	private static List<Integer> normalize(Integer p, Integer q)
	{
		List<Integer> pair;
		if(p<q)
		{
			pair = Arrays.asList(p,q);
		}
		else
		{
			pair = Arrays.asList(q,p);
		}
		return pair;
	}
	
	public static <P,S> SFA<P,S> mooreMinimize(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		if(aut.isEmpty())
		{
			return SFA.getEmptySFA(ba);
		}
		if (!aut.isDeterministic())
		{
			aut = aut.determinize(ba);
		}
		aut = aut.mkTotal(ba);
		int normalizeStateCount = (aut.stateCount()*aut.stateCount())/2;
		HashSet<List<Integer>> neq = new HashSet<List<Integer>>();
		for (Integer p : aut.getFinalStates())
		{
			for (Integer q : aut.getNonFinalStates())
			{
				neq.add(normalize(p,q));
			}
		}
		boolean equivChanged = true;
		while(equivChanged)
		{
			equivChanged = false;
			for (Integer p : aut.getStates())
			{
				for (Integer q : aut.getStates())
				{
					if (q <= p)
					{
						continue;
					}
					List<Integer> pair = Arrays.asList(p,q);
					if (neq.contains(pair))
					{
						continue;
					}
					for(SFAInputMove<P,S> phi : aut.getInputMovesFrom(p))
					{
						P phiGuard = phi.guard;
						for(SFAInputMove<P, S> psi : aut.getInputMovesFrom(q))
						{
							P psiGuard = psi.guard;
							P phiPsiAnd = ba.MkAnd(psiGuard, phiGuard);
							if (ba.IsSatisfiable(phiPsiAnd))
							{
								List<Integer> nextPair = normalize(phi.to, psi.to);
								if (neq.contains(nextPair))
								{
									neq.add(pair);
									equivChanged = true;
								}
							}
						}
					}
				}
			}
		}
		HashMap<Integer, Integer> stateEquiv = new HashMap<Integer, Integer>();
		HashSet<Integer> newStates = new HashSet<Integer>();
		Collection<Integer> newFinalStates = new HashSet<Integer>();
		Integer newInitialState = null;
		for(Integer p : aut.getStates())
		{
			for(Integer q : newStates)
			{
				List<Integer> pair = normalize(p,q);
				if (neq.contains(pair))
				{
					continue;
				}
				else
				{
					stateEquiv.put(p,q);
					if(aut.isInitialState(p))
					{
						newInitialState = q;
					}
				}
			}
			if (!stateEquiv.containsKey(p))//no found equivalence for p
			{
				newStates.add(p);
				stateEquiv.put(p, p);
				if(aut.isFinalState(p))
				{
					newFinalStates.add(p);
				}
				if(aut.isInitialState(p))
				{
					newInitialState = p;
				}
			}
		}
		assert(newInitialState != null);
		Collection<SFAMove<P, S>> newTransitions = new LinkedList<SFAMove<P, S>>();
		for(Integer p : newStates)
		{
			for(SFAInputMove<P,S> t : aut.getInputMovesFrom(p))
			{
				SFAInputMove<P,S> newt = new SFAInputMove<P,S>(p, stateEquiv.get(t.to), t.guard);
				newTransitions.add(newt);
				//System.out.println(newt);
			}
		}
		SFA<P,S> minAut = SFA.MkSFA(newTransitions, newInitialState, newFinalStates, ba);
		return minAut;
	}
}
