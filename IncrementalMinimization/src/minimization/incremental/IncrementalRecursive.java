package minimization.incremental;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import minimization.incremental.IncrementalMinimization.EquivTest;

import org.sat4j.specs.TimeoutException;

import structures.DependencyGraph;
import structures.DisjointSets;
import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;


public class IncrementalRecursive<P,S> extends IncrementalMinimization<P,S>
{
	private class EquivTestRecursive extends EquivTest
	{
		public EquivTestRecursive(DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
		}
		
		public boolean isEquivRecursive(Integer p, Integer q) throws TimeoutException
		{
			if (isKnownNotEqual(p,q))
			{
				return false;
			}
			List<Integer> pair = normalize(p,q);
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
					if (!isEquivRecursive(pNextClass, qNextClass))
					{
						return false;
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
			path.remove(pair);
			equiv.add(pair);
			return true;
		}
		
		@Override
		public boolean isEquiv(Integer pStart, Integer qStart) throws TimeoutException
		{
			boolean finalResult = isEquivRecursive(pStart, qStart);
			return finalResult;
		}
	}
	
	public IncrementalRecursive(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		super(aut,ba);
	}
	
	@Override
	protected EquivTest makeEquivTest(DisjointSets<Integer> equivClasses)
	{
		HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,0.9f);
		HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,0.9f);
		return new EquivTestRecursive(equivClasses, equiv, path);
	}
}
