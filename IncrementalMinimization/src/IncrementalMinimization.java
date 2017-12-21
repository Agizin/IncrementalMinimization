import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import theory.intervals.IntPred;
import theory.intervals.IntegerSolver;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;

public class IncrementalMinimization
{
	private static class EquivTest<P,S>
	{
		private final SFA<P,S> aut;
		private final BooleanAlgebra<P, S> ba;
		private final DisjointSets<Integer> equivClasses;
		
		private HashSet<List<Integer>> neq;
		private HashSet<List<Integer>> equiv;
		private HashSet<List<Integer>> path;
		
		public EquivTest(SFA<P,S> aut, BooleanAlgebra<P,S> ba, DisjointSets<Integer> equivClasses,
				HashSet<List<Integer>> neq, HashSet<List<Integer>> equiv, HashSet<List<Integer>> path)
		{
			this.aut = aut;
			this.ba = ba;
			this.equivClasses = equivClasses;
			this.neq = neq;
			this.equiv = equiv;
			this.path = path;
		}
		
		private List<SFAInputMove<P,S>> findNonDisjointMoves(Collection<SFAInputMove<P, S>> outp, Collection<SFAInputMove<P, S>> outq) throws TimeoutException
		{
			//TODO: look into local minterm generation, can be more efficient?
			assert(!outp.isEmpty() && !outq.isEmpty()); //TODO: remove assertions
			SFAInputMove<P,S> pMove = outp.iterator().next();
			P pGuard = pMove.guard;
			for(SFAInputMove<P,S> qMove : outq)
			{
				P qGuard = qMove.guard;
				P pqAnd = ba.MkAnd(pGuard, qGuard);
				if(ba.IsSatisfiable(pqAnd))
				{
					return Arrays.asList(pMove,qMove);
				}
			}
			return null;
		}
		
		public boolean isEquiv(Integer p, Integer q) throws TimeoutException
		{
			List<Integer> pair = normalize(p,q); //Should already be normalized
			if (neq.contains(pair))
			{
				return false;
			}
			if (path.contains(pair))
			{
				return true;
			}
			path.add(pair);
			Collection<SFAInputMove<P, S>> outp = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(p));
			Collection<SFAInputMove<P, S>> outq = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(q));
			while (!outp.isEmpty() && !outq.isEmpty())
			{
				List<SFAInputMove<P,S>> nonDisjointGuards = findNonDisjointMoves(outp,outq);
				SFAInputMove<P,S> pMove = nonDisjointGuards.get(0);
				SFAInputMove<P,S> qMove = nonDisjointGuards.get(1);
				//note: we don't actually need to generate a witness, only need to know pMove,qMove are non-disjoint
				Integer pNextClass = equivClasses.find(pMove.to);
				Integer qNextClass = equivClasses.find(qMove.to);
				List<Integer> nextPair = normalize(pNextClass, qNextClass);
				if ( !pNextClass.equals(qNextClass) && !equiv.contains(nextPair))
				{
					equiv.add(nextPair);
					if(!isEquiv(pNextClass, qNextClass))
					{
						return false;
					}
					else
					{
						path.remove(nextPair);
					}
				}
				outp.remove(pMove);
				outq.remove(qMove);
				P newPGuard = ba.MkAnd(pMove.guard, ba.MkNot(qMove.guard));
				if (ba.IsSatisfiable(newPGuard))
				{
					outp.add(new SFAInputMove<P, S>(pMove.from, pMove.to, newPGuard));
				}
				P newQGuard = ba.MkAnd(qMove.guard, ba.MkNot(pMove.guard));
				if (ba.IsSatisfiable(newQGuard))
				{
					outq.add(new SFAInputMove<P, S>(qMove.from, qMove.to, newQGuard));
				}
			}
			equiv.add(pair);
			return true;
		}
		
		public HashSet<List<Integer>> getEquiv()
		{
			return equiv;
		}
		
		public HashSet<List<Integer>> getPath()
		{
			return path;
		}
	}
	
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
	
	public static <P, S> SFA<P, S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S>  ba) throws TimeoutException
	{
		if(aut.isEmpty())
		{
			return SFA.getEmptySFA(ba);
		}
		aut = aut.determinize(ba).mkTotal(ba); //TODO: normalizes?
		DisjointSets<Integer> equivClasses = new DisjointSets<Integer>();
		for(Integer q : aut.getStates())
		{
			equivClasses.make(q);
		}
		Integer num_pairs = aut.getStates().size() * aut.getStates().size(); //n^2 where n is # of states
		HashSet<List<Integer>> neq = new HashSet<List<Integer>>(num_pairs, 1); //set is given initial capacity of n^2, won't exceed this
		for(Integer p : aut.getFinalStates())
		{
			for(Integer q : aut.getNonFinalStates())
			{
				neq.add(normalize(p,q));
			}
		}
		
		for(Integer p : aut.getStates())
		{
			for(Integer q : aut.getStates())
			{
				if(q <= p)
				{
					continue;
				}
				List<Integer> pair = Arrays.asList(p,q);
				if(neq.contains(pair))
				{
					continue;
				}
				else if(equivClasses.find(p) == equivClasses.find(q))
				{
					//Already found p,q equivalent
					continue;
				}
				//TODO: look into efficiency of HashSet operations, ideally should be O(1) for searching, inserting, removing
				HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,1);
				HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,1);
				EquivTest<P,S> pEquiv = new EquivTest<P,S>(aut, ba, equivClasses, neq, equiv, path);
				if(pEquiv.isEquiv(p,q))
				{
					//p,q found equivalent. Other pairs may be found equivalent.
					for(List<Integer> equivPair : pEquiv.getEquiv())
					{
						equivClasses.union(equivPair.get(0), equivPair.get(1));
					}
				}
				else
				{
					//p,q found non-equivalent. Other pairs may be found non-equivalent.
					for(List<Integer> pathPair : pEquiv.getPath())
					{
						neq.add(pathPair);
					}
				}
			}
		}
		
		//new SFA created with minimum states
		//TODO verify that this merges transitions correctly.
		HashMap<Integer, HashSet<Integer>> classes = equivClasses.getSets();
		Set<Integer> newStates = classes.keySet();
		Collection<SFAMove<P, S>> newTransitions = new LinkedList<SFAMove<P, S>>();
		Collection<Integer> newFinalStates = new HashSet<Integer>();
		for (Integer p : newStates)
		{
			for (SFAInputMove<P,S> t : aut.getInputMovesFrom(classes.get(p)))
			{
				newTransitions.add(new SFAInputMove<P,S>(p, equivClasses.find(t.to), t.guard));
			}
			if(aut.isFinalState(p))
			{
				newFinalStates.add(p);
			}
		}
		Integer newInitialState = equivClasses.find(aut.getInitialState());
		SFA<P,S> minAut = SFA.MkSFA(newTransitions, newInitialState, newFinalStates, ba, false);
		return minAut;
	}
	
}