import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;

import org.sat4j.specs.TimeoutException;

import theory.BooleanAlgebra;
import theory.intervals.IntPred;
import theory.intervals.IntegerSolver;
import utilities.Pair;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;

public class IncrementalMinimization <P,S>
{
	@SuppressWarnings("rawtypes") // Extensions of Throwable class can not be generic
	private static class TimeBudgetExceeded extends TimeoutException
	{
		private SFA returnAut;
		
		public TimeBudgetExceeded(String message, SFA returnAut)
		{
			super(message);
			this.returnAut = returnAut;
		}
		
		public TimeBudgetExceeded(SFA returnAut)
		{
			this("Time budget exceeded", returnAut);
		}

		public SFA getReturnAut()
		{
			return returnAut;
		}
	}
	
	private class EquivTest
	{
		protected final DisjointSets<Integer> equivClasses;
		
		protected HashSet<List<Integer>> equiv;
		protected HashSet<List<Integer>> path;
		
		public EquivTest(DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			this.equivClasses = equivClasses;
			this.equiv = equiv;
			this.path = path;
		}
		
		private List<SFAInputMove<P,S>> findNonDisjointMoves(Collection<SFAInputMove<P, S>> outp, 
				Collection<SFAInputMove<P, S>> outq) throws TimeoutException
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
			if (isKnownNotEqual(p,q))
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
	
	private class EquivTestUpfront extends EquivTest
	{
		
		private final ArrayList<P> minterms;
		
		public EquivTestUpfront(DisjointSets<Integer> equivClasses, ArrayList<P> minterms, 
				HashSet<List<Integer>> equiv, HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
			this.minterms = minterms;
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
		
		public boolean isEquiv(Integer p, Integer q) throws TimeoutException, TimeBudgetExceeded
		{
			List<Integer> pair = normalize(p,q); //Should already be normalized
			if (isKnownNotEqual(p,q))
			{
				return false;
			}
			if (path.contains(pair))
			{
				return true;
			}
			path.add(pair);
			for (P minterm : minterms)
			{
				Integer pNextClass = equivClasses.find(mintermTransition(p, minterm));
				Integer qNextClass = equivClasses.find(mintermTransition(q, minterm));
				List<Integer> nextPair = normalize(pNextClass, qNextClass);
				if (!pNextClass.equals(qNextClass) && !equiv.contains(nextPair))
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
			}
			equiv.add(pair);
			return true;
		}
		
	}
	
	private class StateComparator implements Comparator<Integer>
	{
	
		public int compare(Integer a, Integer b)
		{
			if (a == b)
			{
				return 0;
			}
			int diff = distanceToFinalMap.get(a) - distanceToFinalMap.get(b);
			if (diff == 0)
			{
				return a - b;
			}
			else
			{
				return diff;
			}
		}
		
	}
	
	public static <P,S> SFA<P,S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S> ba, long budget, boolean upfront) 
			throws TimeoutException
	{
		try
		{
			IncrementalMinimization<P,S> min = new IncrementalMinimization<P,S>(aut, ba);
			return min.minimize(budget, upfront);
		}
		catch(TimeBudgetExceeded e)
		{
			return e.getReturnAut();
		}
	}
	
	public static <P,S> SFA<P,S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S> ba, boolean upfront) throws TimeoutException
	{
		return incrementalMinimize(aut, ba, Long.MAX_VALUE, upfront);
	}
	
	public static <P,S> SFA<P,S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		return incrementalMinimize(aut, ba, Long.MAX_VALUE, false); //Default time budget 200+ years (i.e. there is none)
	}
	
	private final SFA<P,S> aut;
	private final BooleanAlgebra<P,S> ba;
	private final int num_pairs;
	
	private HashSet<List<Integer>> neq;
	private LinkedHashMap<Integer, Integer> distanceToFinalMap;
	private StateComparator stateComp;
	
	public IncrementalMinimization(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		if (!aut.isDeterministic())
		{
			aut = aut.determinize(ba);
		}
		this.aut = aut.mkTotal(ba);
		this.ba = ba;
		this.num_pairs = aut.getStates().size() * aut.getStates().size();
		this.neq = new HashSet<List<Integer>>(num_pairs, 0.9f); //won't exceed initial capacity
		this.distanceToFinalMap = generateDistanceToFinalMap();
		this.stateComp = new StateComparator();
	}
	
	private LinkedHashMap<Integer, Integer> generateDistanceToFinalMap()
	{
		class StateInfo
		{
			public final Integer stateID;
			public final Integer distanceToFinal;
			
			public StateInfo(Integer stateID, Integer distanceToFinal)
			{
				this.stateID = stateID;
				this.distanceToFinal = distanceToFinal;
			}
			
			public String toString()
			{
				return String.format("(%d, %d)", stateID, distanceToFinal);
			}
		}
		
		LinkedHashMap<Integer, Integer> distanceMap = new LinkedHashMap<Integer, Integer>();
		HashSet<Integer> visitedStates = new HashSet<Integer>();
		Queue<StateInfo> stateQueue = new LinkedList<StateInfo>();
		
		for(Integer finalState : aut.getFinalStates())
		{
			stateQueue.add(new StateInfo(finalState, 0));
			visitedStates.add(finalState);
		}
		while(!stateQueue.isEmpty())
		{
			StateInfo s = stateQueue.poll();
			distanceMap.put(s.stateID, s.distanceToFinal);
			Integer nextDistance = s.distanceToFinal + 1;
			for (SFAInputMove<P,S> t : aut.getInputMovesTo(s.stateID))
			{
				Integer nextState = t.from;
				if(!visitedStates.contains(nextState))
				{
					stateQueue.add(new StateInfo(nextState, nextDistance));
					visitedStates.add(nextState);
				}
			}
		}
		
		for(Integer state : aut.getNonFinalStates())
		{
			if (!visitedStates.contains(state))
			{
				assert(!distanceMap.containsKey(state)); //TODO: remove this
				distanceMap.put(state, Integer.MAX_VALUE); //indicates sink state
			}
		}
		
		return distanceMap;
	}
	
	private List<Integer> normalize(Integer p, Integer q)
	{
		List<Integer> pair;
		if(stateComp.compare(p, q) < 0)
		{
			pair = Arrays.asList(p,q);
		}
		else
		{
			pair = Arrays.asList(q,p);
		}
		return pair;
	}
	
	private boolean isSinkState(Integer p)
	{
		return distanceToFinalMap.get(p) == Integer.MAX_VALUE;
	}
	
	private boolean isKnownNotEqual(Integer p, Integer q)
	{
		if (neq.contains(normalize(p,q)))
		{
			return true;
		}
		else if (!distanceToFinalMap.get(p).equals(distanceToFinalMap.get(q)))
		{
			neq.add(normalize(p,q));
			return true;
		}
		else
		{
			return false;
		}
	}
	
	private SFA<P,S> mergeSFAStates(DisjointSets<Integer> equivClasses) throws TimeoutException
	{
		//new SFA created with minimum states
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
	
	private void timeCheck(long endTime, DisjointSets<Integer> equivClasses) throws TimeoutException
	{
		if(System.nanoTime() > endTime)
		{
			//Time Budget exceeded
			SFA<P,S> curAut = mergeSFAStates(equivClasses);
			double exceeded = (new Double(System.nanoTime()-endTime))/1000000;
			System.out.println(String.format("Exceeded by %f ms", exceeded));
			throw new TimeBudgetExceeded(curAut);
			/* Current time budget implementation intended to test % of automata minimization given
			 * a set period of time. However, it does not necessarily return this mostly minimized
			 * automata exactly after the budget is met (this is deinitiely possible, just not with
			 * present implementation).
			 */
		}
	}
	
	public SFA<P, S> minimize(long budget, boolean upfront) 
			throws TimeoutException
	{
		long endTime = System.nanoTime() + budget;
		if (endTime < 0) //indicates overflow
		{
			endTime = Long.MAX_VALUE;
		}
		if(aut.isEmpty())
		{
			return SFA.getEmptySFA(ba);
		}
		ArrayList<P> upfront_minterms = null;
		if(upfront)
		{
			upfront_minterms = MintermTree.generate_minterms(aut, ba);
		}
		DisjointSets<Integer> equivClasses = new DisjointSets<Integer>();
		for(Integer q : aut.getStates())
		{
			equivClasses.make(q);
		}
		for(Integer p : distanceToFinalMap.keySet())
		{
			for(Integer q : distanceToFinalMap.keySet())
			{
				if(stateComp.compare(q,p) <= 0)
				{
					if (distanceToFinalMap.get(p) < distanceToFinalMap.get(q))
					{
						break; //All later qs will be inequivalent
					}
					else
					{
						continue;
					}
				}
				if(isKnownNotEqual(p,q))
				{
					continue;
				}
				else if(equivClasses.find(p) == equivClasses.find(q))
				{
					//Already found p,q equivalent
					continue;
				}
				//TODO: look into efficiency of HashSet operations, ideally should be O(1) for searching, inserting, removing
				HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,0.9f);
				HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,0.9f);
				timeCheck(endTime, equivClasses);
				EquivTest pEquiv;
				if(!upfront)
				{
					pEquiv = new EquivTest(equivClasses, equiv, path);

				}
				else
				{
					pEquiv = new EquivTestUpfront(equivClasses, upfront_minterms, equiv, path);
				}
				boolean isequiv = pEquiv.isEquiv(p, q);
				equiv = pEquiv.getEquiv();
				path = pEquiv.getPath();
				if(isequiv)
				{
					//p,q found equivalent. Other pairs may be found equivalent.
					for(List<Integer> equivPair : equiv)
					{
						equivClasses.union(equivPair.get(0), equivPair.get(1));
						//equivClasses.union(equivPair.get(0), equivPair.get(1));
					}
					timeCheck(endTime, equivClasses);
					//after equiv merging for soft time budget?
				}
				else
				{
					timeCheck(endTime, equivClasses);
					//p,q found non-equivalent. Other pairs may be found non-equivalent.
					for(List<Integer> pathPair : path)
					{
						neq.add(pathPair);
					}
				}
			}
		}
		
		return mergeSFAStates(equivClasses);
	}
	
	
	
}
