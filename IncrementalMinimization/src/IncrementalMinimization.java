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
import utilities.Pair;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;

public class IncrementalMinimization
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
	
	private static class EquivTestUpfront<P,S>
	{
		private static class MintermTree<P,S>
		{
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
						this.left = new MintermTree(ba, predAnd);
						this.right = new MintermTree(ba, predAndNot);
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
		
		public static <P,S> ArrayList<P> generate_minterms(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
		{	
			MintermTree<P,S> tree = new MintermTree(ba, ba.True());
			for(SFAInputMove<P,S> p : aut.getInputMovesFrom(aut.getStates()))
			{
				tree.refine(p.guard);
			}
			return tree.getMinterms();
		}
		
		private final SFA<P,S> aut;
		private final BooleanAlgebra<P, S> ba;
		private final DisjointSets<Integer> equivClasses;
		private final ArrayList<P> minterms;
		
		private HashSet<List<Integer>> neq;
		private HashSet<List<Integer>> equiv;
		private HashSet<List<Integer>> path;
		
		public EquivTestUpfront(SFA<P,S> aut, BooleanAlgebra<P,S> ba, DisjointSets<Integer> equivClasses,
				ArrayList<P> minterms, HashSet<List<Integer>> neq, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			this.aut = aut;
			this.ba = ba;
			this.equivClasses = equivClasses;
			this.minterms = minterms;
			this.neq = neq;
			this.equiv = equiv;
			this.path = path;
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
			if (neq.contains(pair))
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
	
	private static <P,S> SFA<P,S> mergeSFAStates(DisjointSets<Integer> equivClasses, 
			SFA<P,S> originalAut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		//new SFA created with minimum states
		HashMap<Integer, HashSet<Integer>> classes = equivClasses.getSets();
		Set<Integer> newStates = classes.keySet();
		Collection<SFAMove<P, S>> newTransitions = new LinkedList<SFAMove<P, S>>();
		Collection<Integer> newFinalStates = new HashSet<Integer>();
		for (Integer p : newStates)
		{
			for (SFAInputMove<P,S> t : originalAut.getInputMovesFrom(classes.get(p)))
			{
				newTransitions.add(new SFAInputMove<P,S>(p, equivClasses.find(t.to), t.guard));
			}
			if(originalAut.isFinalState(p))
			{
				newFinalStates.add(p);
			}
		}
		Integer newInitialState = equivClasses.find(originalAut.getInitialState());
		SFA<P,S> minAut = SFA.MkSFA(newTransitions, newInitialState, newFinalStates, ba, false);
		return minAut;
	}
	
	private static <P, S> void timeCheck(SFA<P,S> aut, BooleanAlgebra<P,S> ba, 
			DisjointSets<Integer> equivClasses, long endTime) throws TimeoutException
	{
		if(System.nanoTime() > endTime)
		{
			//Time Budget exceeded
			SFA<P,S> curAut = mergeSFAStates(equivClasses, aut, ba);
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
	
	public static <P, S> SFA<P, S> minimize(SFA<P,S> aut, BooleanAlgebra<P,S>  ba, long budget, boolean upfront) 
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
		if (!aut.isDeterministic())
		{
			aut = aut.determinize(ba);
		}
		aut = aut.mkTotal(ba);
		ArrayList<P> upfront_minterms = null;
		if(upfront)
		{
			upfront_minterms = EquivTestUpfront.generate_minterms(aut, ba);
		}
		int num_pairs = aut.getStates().size() * aut.getStates().size(); //n^2 where n is # of states
		DisjointSets<Integer> equivClasses = new DisjointSets<Integer>();
		for(Integer q : aut.getStates())
		{
			equivClasses.make(q);
		}
		HashSet<List<Integer>> neq = new HashSet<List<Integer>>(num_pairs, 0.9f); //set is given initial capacity of n^2, won't exceed this
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
				HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,0.9f);
				HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,0.9f);
				timeCheck(aut, ba, equivClasses, endTime);
				boolean isequiv;
				if(!upfront)
				{
					EquivTest<P,S> pEquiv = new EquivTest<P,S>(aut, ba, equivClasses, neq, equiv, path);
					isequiv = pEquiv.isEquiv(p, q);
					equiv = pEquiv.getEquiv();
					path = pEquiv.getPath();
				}
				else
				{
					EquivTestUpfront<P, S> pEquivUpfront = new EquivTestUpfront<P,S>(aut, ba, equivClasses,
							upfront_minterms, neq, equiv, path);
					isequiv = pEquivUpfront.isEquiv(p,q);
					equiv = pEquivUpfront.getEquiv();
					path = pEquivUpfront.getPath();
				}
				if(isequiv)
				{
					//p,q found equivalent. Other pairs may be found equivalent.
					for(List<Integer> equivPair : equiv)
					{
						equivClasses.union(equivPair.get(0), equivPair.get(1));
						//equivClasses.union(equivPair.get(0), equivPair.get(1));
					}
					timeCheck(aut, ba, equivClasses, endTime);
					//after equiv merging for soft time budget?
				}
				else
				{
					timeCheck(aut, ba, equivClasses, endTime);
					//p,q found non-equivalent. Other pairs may be found non-equivalent.
					for(List<Integer> pathPair : path)
					{
						neq.add(pathPair);
					}
				}
			}
		}
		
		return mergeSFAStates(equivClasses, aut, ba);
	}
	
	public static <P,S> SFA<P,S> incrementalMinimize(SFA<P,S> aut, BooleanAlgebra<P,S> ba, long budget, boolean upfront) 
			throws TimeoutException
	{
		try
		{
			return minimize(aut, ba, budget, upfront);
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
	//TODO: refactor, make class instantiable with above as constructors.
	
}
