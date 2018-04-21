package structures;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.sat4j.specs.TimeoutException;

public class DependencyGraph 
{
	protected class StatePair //Nodes in graph
	{
		public final List<Integer> pair;
		private boolean isTested;
		private LinkedList<StatePair> deps; //successor nodes, i.e. pairs that this pair is dependent on

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

	public DependencyGraph()
	{
		this.pairLookup = new HashMap<List<Integer>,StatePair>();
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
	
	private int mergePair(StatePair pairEntry, DisjointSets<Integer> equivClasses, 
			HashSet<List<Integer>> badPairs) throws TimeoutException
	{
		
		Queue<StatePair> depQueue = new LinkedList<StatePair>();
		depQueue.addAll(pairEntry.getDependencies());
		HashSet<StatePair> seenPairs = new HashSet<StatePair>();
		while(!depQueue.isEmpty())
		{
			StatePair dep = depQueue.remove();
			if(seenPairs.contains(dep) ||
					equivClasses.find(dep.pair.get(0)) == equivClasses.find(dep.pair.get(1)))
			{
				continue;
			}
			seenPairs.add(dep);
			if(!dep.isTested() || badPairs.contains(dep.pair))
			{
				return 0;
			}
			depQueue.addAll(dep.getDependencies());
		}
		for(StatePair mergePair : seenPairs)
		{
			equivClasses.union(mergePair.pair.get(0), mergePair.pair.get(1));
		}
		return seenPairs.size();
	}
	
	public int mergeStates(DisjointSets<Integer> equivClasses, HashSet<List<Integer>> badPath) throws TimeoutException
	{
		int result = 0;
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
				result += mergePair(pairEntry,equivClasses,badPath);
			}
		}
		return result;
	}
}
