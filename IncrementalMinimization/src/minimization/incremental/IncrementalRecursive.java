package minimization.incremental;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import minimization.incremental.IncrementalMinimization.EquivTest;

import org.sat4j.specs.TimeoutException;

import structures.DisjointSets;
import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;


public class IncrementalRecursive<P,S> extends IncrementalMinimization<P,S>
{
	private class EquivTestRecursive extends EquivTest
	{
		private class ResultDependencies
		{
			private boolean result;
			private boolean isindependent;
			private HashMap<List<Integer>, Boolean> dependencyTest; //List of pairs of states that must be equivalent for current result to hold.
			private HashSet<List<Integer>> dependencies;
			
			public ResultDependencies(boolean result)
			{
				this.result = result;
				this.isindependent = true;
				this.dependencyTest = new HashMap<List<Integer>, Boolean>();
				this.dependencies = new HashSet<List<Integer>>();
			}
			
			public ResultDependencies(boolean result, List<Integer> dependency)
			{
				this(result);
				addDependency(dependency);
				this.isindependent = false;
			}
			
			public boolean resultIsIndependent()
			{
				return isindependent;
			}
			
			public void addDependency(List<Integer> pair)
			{
				if (isEquiv())
				{
					dependencyTest.put(pair, false);
					dependencies.add(pair);
					isindependent = false;
				}
				else
				{
					throw new IllegalStateException("False result has no dependencies");
				}
			}
			
			public void removeDependency(List<Integer> pair)
			{
				dependencyTest.put(pair, true);
				dependencies.remove(pair);
				if (dependencies.isEmpty())
				{
					isindependent = true;
				}
			}
			
			public boolean isDependency(List<Integer> pair)
			{
				return dependencies.contains(pair);
			}
			
			public void combineWithResult(ResultDependencies other)
			{
				result = result && other.isEquiv();
				if(!result)
				{
					dependencies.clear();
				}
				else
				{
					HashMap<List<Integer>, Boolean> otherDepends = other.getDependencyTests();
					for (List<Integer> pair : otherDepends.keySet())
					{
						Boolean otherSatisfied = otherDepends.get(pair);
						if(otherSatisfied)
						{
							removeDependency(pair);
						}
						else
						{
							if(!dependencyTest.containsKey(pair))
							{
								addDependency(pair);
							}
							else
							{
								if(!dependencyTest.get(pair))
								{
									assert(isDependency(pair));
								}
							}
						}
					}
				}
			}
			
			public boolean isEquiv()
			{
				return result;
			}
			
			public HashMap<List<Integer>, Boolean> getDependencyTests()
			{
				return dependencyTest;
			}

			public void updateDepenencies() 
			{
				List<List<Integer>> checked = new LinkedList<List<Integer>>();
				for (List<Integer> pair : dependencies)
				{
					if(!path.contains(pair))
					{
						dependencyTest.put(pair, true);
						checked.add(pair);
					}
				}
				dependencies.removeAll(checked);
			}
		}
		
		private HashMap<List<Integer>, ResultDependencies> equivDepends;
		
		public EquivTestRecursive(DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
			this.equivDepends = new HashMap<List<Integer>, ResultDependencies>();
		}
		
		public ResultDependencies isEquivRecursive(Integer p, Integer q) throws TimeoutException
		{
			if (isKnownNotEqual(p,q))
			{
				return new ResultDependencies(false);
			}
			List<Integer> pair = normalize(p,q);
			if (path.contains(pair))
			{
				ResultDependencies r = new ResultDependencies(true);
				r.addDependency(pair);
				return r;
			}
			path.add(pair);
			Collection<SFAInputMove<P, S>> outp = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(p));
			Collection<SFAInputMove<P, S>> outq = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(q));
			ResultDependencies thisResult = new ResultDependencies(true);
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
					equivDepends.put(nextPair, null);
					if(path.contains(nextPair))
					{
						thisResult.addDependency(nextPair);
					}
					else
					{
						ResultDependencies nextResult = isEquivRecursive(pNextClass, qNextClass);
						if(!nextResult.isEquiv())
						{
							return nextResult;
						}
						else
						{
							equivDepends.put(nextPair, nextResult);
							path.remove(nextPair);
							thisResult.combineWithResult(nextResult);
						}
					}
				}
				else if (equiv.contains(nextPair))
				{
					ResultDependencies dependencies = equivDepends.get(nextPair);
					if (dependencies == null && !pair.equals(nextPair))
					{
						thisResult.addDependency(nextPair);
					}
					else if(!pair.equals(nextPair))
					{
						thisResult.combineWithResult(dependencies);
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
			thisResult.removeDependency(pair);
			thisResult.updateDepenencies();
			if(thisResult.resultIsIndependent())
			{
				equivClasses.union(p,q);
			}
			else
			{
				equiv.add(pair);
				equivDepends.put(pair, thisResult);
			}
			return thisResult;
		}
		
		@Override
		public boolean isEquiv(Integer pStart, Integer qStart) throws TimeoutException
		{
			ResultDependencies finalResult = isEquivRecursive(pStart, qStart);
			return finalResult.isEquiv();
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
