import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.apache.commons.lang3.NotImplementedException;
import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import theory.intervals.IntPred;
import theory.intervals.IntegerSolver;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;

public class Main
{
	private static class EquivTest<P,S>
	{
		private SFA<P,S> aut;
		private HashSet<Integer[]> equiv;
		private HashSet<Integer[]> path;
		
		public EquivTest(SFA<P,S> aut, HashSet<Integer[]> equiv, HashSet<Integer[]> path)
		{
			this.aut = aut;
			this.equiv = equiv;
			this.path = path;
		}
		
		public boolean isEquiv(Integer p, Integer q) throws NotImplementedException
		{
			//TODO
			throw new NotImplementedException("Incremental Equivalence Not Implemented Yet");
		}
		
		public HashSet<Integer[]> getEquiv()
		{
			return equiv;
		}
		
		public HashSet<Integer[]> getPath()
		{
			return path;
		}
	}
	
	private static Integer[] normalize(Integer p, Integer q)
	{
		Integer[] pair;
		if(p<q)
		{
			pair = new Integer[]{p,q};
		}
		else
		{
			pair = new Integer[]{q,p};
		}
		return pair;
	}
	
	public static <P, S> SFA<P, S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S>  ba) throws TimeoutException
	{
		if(aut.isEmpty())
		{
			return SFA.getEmptySFA(ba);
		}
		aut = aut.determinize(ba).mkTotal(ba);
		DisjointSets<Integer> equivClasses = new DisjointSets<Integer>();
		for(Integer q : aut.getStates())
		{
			equivClasses.make(q);
		}
		Integer num_pairs = aut.getStates().size() * aut.getStates().size(); //n^2 where n is # of states
		HashSet<Integer[]> neq = new HashSet<Integer[]>(num_pairs, 1); //set is given initial capacity of n^2, won't exceed this
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
				Integer[] pair = new Integer[]{p,q};
				if(neq.contains(pair))
				{
					//Already know p,q not equivalent
					continue;
				}
				else if(equivClasses.find(p) == equivClasses.find(q))
				{
					//Already found p,q equivalent
					continue;
				}
				
				//TODO: look into efficiency of HashSet operations, ideally should be O(1) for searching, inserting, removing
				HashSet<Integer[]> equiv = new HashSet<Integer[]>(num_pairs,1);
				HashSet<Integer[]> path = new HashSet<Integer[]>(num_pairs,1);
				EquivTest<P,S> pEquiv = new EquivTest<P,S>(aut, equiv, path);
				if(pEquiv.isEquiv(p,q))
				{
					//p,q found equivalent. Other pairs may be found equivalent.
					for(Integer[] equivPair : pEquiv.getEquiv())
					{
						equivClasses.union(equivPair[0], equivPair[1]);
					}
				}
				else
				{
					//p,q found non-equivalent. Other pairs may be found non-equivalent.
					for(Integer[] pathPair : pEquiv.getPath())
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
		return SFA.MkSFA(newTransitions, newInitialState, newFinalStates, ba);
	}
	
	public static void main(String[] args) throws TimeoutException
	{
		//TODO: move tests to separate class
		
		//our algebra is constructed
		IntegerSolver ba = new IntegerSolver();
		IntPred neg = new IntPred(null, new Integer(0));
		IntPred less_neg_ten = new IntPred(null, new Integer(-10));
		IntPred great_pos_ten = new IntPred(new Integer(10), null);
		IntPred zero = new IntPred(new Integer(0));
		IntPred one = new IntPred(1);
		IntPred zero_five = new IntPred(new Integer(0), new Integer(5));
		IntPred pos = new IntPred(new Integer(1), null);
		
		//transitions are defined
		Collection <SFAMove<IntPred,Integer>> transitions = new LinkedList<SFAMove<IntPred, Integer>>();
		IntPred a_pred = ba.MkAnd(ba.MkNot(one), ba.MkNot(zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,0,a_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,1,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,2,one));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,0,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,1,a_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,2,one));
		IntPred b_pred = ba.MkAnd(pos, ba.MkNot(zero_five));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,2,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,3,neg));
		IntPred c_pred = ba.MkAnd(ba.MkNot(zero), zero_five);
		transitions.add(new SFAInputMove<IntPred, Integer>(2,5,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,6,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(3,3,ba.True()));
		transitions.add(new SFAInputMove<IntPred, Integer>(4,4,ba.True()));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,3, neg));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,3,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,6,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,7,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,4,neg));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,4,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,5,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,7,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,1,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,4,ba.MkNot(c_pred)));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,8,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,0,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,3,ba.MkNot(c_pred)));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,7,c_pred));
		
		//SFA is defined
		SFA<IntPred, Integer> aut = SFA.MkSFA(transitions, 0, Arrays.asList(7,8), ba);
		
		//SFA is tested
		assert(aut.accepts(Arrays.asList(1,7,10),ba));
		assert(aut.isDeterministic(ba));
		assert(aut.isTotal());

		
		SFA<IntPred, Integer> minAut = incrementalMinimize(aut, ba);
	}
}
