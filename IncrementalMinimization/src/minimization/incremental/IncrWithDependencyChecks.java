package minimization.incremental;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import minimization.incremental.IncrementalMinimization.EquivTest;

import org.sat4j.specs.TimeoutException;

import structures.DisjointSets;
import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;

public class IncrWithDependencyChecks<P,S> extends IncrementalMinimization<P,S>
{

	protected class EquivTestDependency extends EquivTest //tests for equality of two given states in the automata
	{
		protected class Dependencies
		{
			private HashMap<List<Integer>,ArrayList<List<Integer>>> dependencies;
			private HashSet<List<Integer>> satisfiedDeps;
			
			public Dependencies()
			{
				this.dependencies = new HashMap<List<Integer>,ArrayList<List<Integer>>>();
				this.satisfiedDeps = new HashSet<List<Integer>>();
			}
			
			public void addDependency(List<Integer> pair, List<Integer> dependency)
			{
				if(dependencies.containsKey(dependency) && !pair.equals(dependency))
				{
					ArrayList<List<Integer>> addDependencyList = dependencies.get(dependency);
					if(!dependencies.containsKey(pair))
					{
						dependencies.put(pair, new ArrayList<List<Integer>>());
					}
					ArrayList<List<Integer>> currentDeps = dependencies.get(pair);
					for(List<Integer> depPair : addDependencyList)
					{
						if(!satisfiedDeps.contains(depPair))
						{
							currentDeps.add(depPair);
							assert(dependencies.get(pair).contains(depPair)); //TODO: remove
						}
					}
				}
				else if(!satisfiedDeps.contains(dependency))
				{
					if(!dependencies.containsKey(pair))
					{
						dependencies.put(pair, new ArrayList<List<Integer>>());
					}
					dependencies.get(pair).add(dependency);
				}
			}
			
			public void addAllDependencies(List<Integer> pair, ArrayList<List<Integer>> dpairs)
			{
				for(List<Integer> dpair : dpairs)
				{
					addDependency(pair, dpair);
				}
			}
			
			public void satisfyDependency(List<Integer> dependency)
			{
				satisfiedDeps.add(dependency);
			}
			
			public void removeDependency(List<Integer> pair, List<Integer> dependency)
			{
				dependencies.remove(pair, dependency);
				satisfyDependency(dependency);
			}
			
			public ArrayList<List<Integer>> getDependencies(List<Integer> pair)
			{
				return dependencies.get(pair);
			}
			
			public boolean isIndependent(List<Integer> pair)
			{
				if(dependencies.containsKey(pair))
				{
					ArrayList<List<Integer>> pairDependencies = dependencies.get(pair);
					for(int i=0; i<pairDependencies.size(); i++)
					{
						if(!satisfiedDeps.contains(pairDependencies.get(i)))
						{
							return false;
						}
						else
						{
							pairDependencies.remove(i);
						}
					}
					assert(pairDependencies.isEmpty());
					assert(dependencies.get(pair).isEmpty());
					return true;
				}
				return false;
			}
		}
		
		public EquivTestDependency (DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
		}
		
		public boolean isEquiv(Integer pStart, Integer qStart) throws TimeoutException
		{
			if (isKnownNotEqual(pStart,qStart))
			{
				return false;
			}
			EquivRecord start = new EquivRecord(pStart,qStart,path);
			Stack<EquivRecord> testStack = new Stack<EquivRecord>();
			testStack.add(start);
			Dependencies deps = new Dependencies();
			while (!testStack.isEmpty())
			{
				EquivRecord curEquivTest = testStack.pop();
				Integer p = curEquivTest.pState;
				Integer q = curEquivTest.qState;
				HashSet<List<Integer>> curPath = curEquivTest.curPath;
				List<Integer> pair = normalize(p,q);
				HashSet<List<Integer>> newPath = new HashSet<List<Integer>>(curPath);
				newPath.add(pair);
				Collection<SFAInputMove<P,S>> outp = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(p));
				Collection<SFAInputMove<P,S>> outq = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(q));
				while(!outp.isEmpty() && !outq.isEmpty())
				{			
					List<SFAInputMove<P,S>> nonDisjointGuards = findNonDisjointMoves(outp, outq);
					SFAInputMove<P,S> pMove = nonDisjointGuards.get(0);
					SFAInputMove<P,S> qMove = nonDisjointGuards.get(1);
					Integer pNextClass = equivClasses.find(pMove.to);
					Integer qNextClass = equivClasses.find(qMove.to);
					List<Integer> nextPair = normalize(pNextClass, qNextClass);
					if(!pNextClass.equals(qNextClass) && !equiv.contains(nextPair))
					{
						if(isKnownNotEqual(pNextClass,qNextClass))
						{
							this.path = newPath;
							return false;
						}
						if (!newPath.contains(nextPair))
						{
							equiv.add(nextPair); 
							EquivRecord nextTest = new EquivRecord(pNextClass, qNextClass, newPath);
							testStack.push(nextTest);
							deps.addDependency(pair, nextPair);
						}
					}
					else if(equiv.contains(nextPair))
					{
						deps.addDependency(pair, nextPair);
					}
					outp.remove(pMove);
					outq.remove(qMove);
					P newPGuard = ba.MkAnd(pMove.guard, ba.MkNot(qMove.guard));
					if (ba.IsSatisfiable(newPGuard))
					{
						outp.add(new SFAInputMove<P,S>(pMove.from, pMove.to, newPGuard));
					}
					P newQGuard = ba.MkAnd(qMove.guard, ba.MkNot(pMove.guard));
					if (ba.IsSatisfiable(newQGuard))
					{
						outq.add(new SFAInputMove<P,S>(qMove.from, qMove.to, newQGuard));
					}
				}
				deps.satisfyDependency(pair);
				if(deps.isIndependent(pair))
				{
					equivClasses.union(p,q);
				}
			}
			equiv.add(normalize(pStart, qStart));
			return true;
		}
	}
	
	public IncrWithDependencyChecks(SFA<P,S> aut, BooleanAlgebra<P,S> ba) throws TimeoutException
	{
		super(aut,ba);
	}
	
	@Override
	protected EquivTest makeEquivTest(DisjointSets<Integer> equivClasses)
	{
		HashSet<List<Integer>> equiv = new HashSet<List<Integer>>(num_pairs,0.9f);
		HashSet<List<Integer>> path = new HashSet<List<Integer>>(num_pairs,0.9f);
		return new EquivTestDependency(equivClasses, equiv, path);
	}
}
