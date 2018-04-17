package minimization.incremental;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
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
		
		protected class Dependencies //tracks the pairs of states that an equivalence result depends on within our algorithm.
		{
			protected class StatePair
			{
				public final List<Integer> pair;
				private boolean isTested;
				private LinkedList<StatePair> deps;
				
				public StatePair(List<Integer> pair, boolean isTested)
				{
					this.pair = pair;
					this.isTested = isTested;
					this.deps = new LinkedList<StatePair>();
				}
				
				public StatePair(List<Integer> pair)
				{
					this(pair, true);
				}
				
				public void addDependency(StatePair dep)
				{
					assert(dep != null);
					deps.add(dep);
				}
				
				public LinkedList<StatePair> getDependencies()
				{
					return deps;
				}
				
				public boolean isTested()
				{
					return isTested;
				}
				
				public void setTested(boolean b)
				{
					isTested = b;
				}
				
				@Override
				public boolean equals(Object other)
				{
					if(other == null || (other.getClass() != getClass()))
					{
						return false;
					}
					StatePair otherPair = (StatePair) other;
					if(pair.equals((otherPair.pair)))
					{
						assert(deps.equals(otherPair.getDependencies()));
						return true;
					}
					else
					{
						return false;
					}
				}
				
				@Override
				public int hashCode()
				{
					return pair.hashCode();
				}
				
				@Override
				public String toString()
				{
					return String.format("%s | %s ", pair.toString(), Boolean.toString(isTested));
				}
				
				public String toStringLong()
				{
					return String.format("%s | %s | %s", pair.toString(), Boolean.toString(isTested), deps.toString());
				}
			}
			
			
			private HashMap<List<Integer>,StatePair> pairLookup;
			
			public Dependencies()
			{
				this.pairLookup = new HashMap<List<Integer>,StatePair>(num_pairs);
			}
			
			public void addDependency(List<Integer> pair, List<Integer> dependency)
			{
				if(pair.equals(dependency))
				{
					return;
				}
				StatePair pairEntry;
				if(pairLookup.containsKey(pair))
				{
					pairEntry = pairLookup.get(pair);
					pairEntry.setTested(true);
				}
				else
				{
					pairEntry = new StatePair(pair, true);
					pairLookup.put(pair, pairEntry);
				}
				StatePair depEntry;
				if(pairLookup.containsKey(dependency))
				{
					depEntry = pairLookup.get(dependency);
				}
				else
				{
					depEntry = new StatePair(dependency, false);
					pairLookup.put(dependency, depEntry);
				}
				assert(depEntry != null);
				pairEntry.addDependency(depEntry);
			}
			
			public void addAllDependencies(List<Integer> pair, ArrayList<List<Integer>> dpairs)
			{
				for(List<Integer> dpair : dpairs)
				{
					addDependency(pair, dpair);
				}
			}
			
			private void mergePair(StatePair pairEntry, HashSet<List<Integer>> badPath) throws TimeoutException
			{
				
				Queue<StatePair> depQueue = new LinkedList<StatePair>();
				depQueue.addAll(pairEntry.getDependencies());
				//HashSet<List<Integer>> debugTest = new HashSet<List<Integer>>();
				HashSet<StatePair> seenPairs = new HashSet<StatePair>();
				while(!depQueue.isEmpty())
				{
					StatePair dep = depQueue.remove();
					assert(! (dep == null));
					if(seenPairs.contains(dep))
					{
						continue;
					}
					seenPairs.add(dep);
					if(!dep.isTested())
					{
						return;
					}
					if(badPath.contains(dep.pair))
					{
						return;
					}
					assert(pairLookup.values().contains(dep));
					depQueue.addAll(dep.getDependencies());
				}
				System.out.println("SQUIBLLITY DOOP BOP"); //unique string for debug purposes
				equivClasses.union(pairEntry.pair.get(0), pairEntry.pair.get(1));
			}
			
			public void mergeStates(HashSet<List<Integer>> badPath) throws TimeoutException
			{
				for(StatePair pairEntry : pairLookup.values())
				{
					if(!pairEntry.isTested)
					{
						continue;
					}
					else if(badPath.contains(pairEntry.pair))
					{
						continue;
					}
					else
					{
						mergePair(pairEntry,badPath);
					}
				}
			}
		}
		
		private Dependencies deps;
		
		public EquivTestDependency (DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path, Dependencies deps)
		{
			super(equivClasses, equiv, path);
			this.deps = deps;
		}
		
		public EquivTestDependency (DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
			this.deps = new Dependencies();
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
					if(equiv.contains(nextPair) || path.contains(nextPair))
					{
						deps.addDependency(pair, nextPair);
					}
					else if(!pNextClass.equals(qNextClass))
					{
						if(isKnownNotEqual(pNextClass,qNextClass))
						{
							newPath.add(nextPair);
							for(List<Integer> pathPair : path)
							{
								neq.add(pathPair); //TODO: remove this call from outer minimize method
							}
							this.path = newPath;
							deps.mergeStates(newPath);
							return false;
						}
						else
						{
							equiv.add(nextPair);
							EquivRecord nextTest = new EquivRecord(pNextClass, qNextClass, newPath);
							testStack.add(nextTest);
						}
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
