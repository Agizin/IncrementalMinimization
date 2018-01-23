import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;


public class DisjointSets <E>
{
	//TODO: rewrite or find an implementation using "rooted trees" for optimization
	
	//implementation inspired from https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-046j-design-and-analysis-of-algorithms-spring-2012/lecture-notes/MIT6_046JS12_lec16.pdf
	//parentMap contains a forest of implicit trees with the identifiers of the sets at the root, every element in parentMap is mapped to its parent in its tree
	

	private HashMap<E, E> parentMap;
	private HashMap<E, Integer> rankMap;
	
	public DisjointSets()
	{
		parentMap = new HashMap<E, E>();
		rankMap = new HashMap<E, Integer>();
	}
	
	public DisjointSets(Collection<E> identifiers)
	{
		parentMap = new HashMap<E, E>();
		rankMap = new HashMap<E, Integer>();
		for(E identifier : identifiers)
		{
			make(identifier);
		}
	}
	
	public void make(E identifier) throws IllegalArgumentException
	{
		if(!parentMap.containsKey(identifier))
		{
			parentMap.put(identifier, null);
			rankMap.put(identifier, 1);
		}
		else
		{
			throw new IllegalArgumentException("Identifier already exists in a set");
		}
	}
	
	public E find(E element) throws IllegalArgumentException
	{
		if (!parentMap.containsKey(element))
		{
			throw new IllegalArgumentException("Element not found in any disjoint set");
		}
		ArrayList<E> path = new ArrayList<E>(53); //height of tree will not exceed 53 with less than 1024 TB of available memory
		while(parentMap.get(element) != null)
		{
			path.add(element);
			element = parentMap.get(element);
			
		}
		for(E pathMember : path) //path is compressed
		{
			if (pathMember != element)
			{
				parentMap.put(pathMember, element);
			}
		}
		return element;
	}
	
	public E union(E elem1, E elem2)
	{
		E iden1 = find(elem1);
		E iden2 = find(elem2);
		E union_iden;
		if(iden1.equals(iden2))
		{
			union_iden = iden1;
		}
		else
		{
			int rank1 = rankMap.get(iden1);
			int rank2 = rankMap.get(iden2);
			if (rank1 == rank2)
			{
				parentMap.put(iden2, iden1);
				rankMap.put(iden1, rank1+1);
				union_iden = iden1;
			}
			else if (rank1 > rank2)
			{
				parentMap.put(iden2, iden1);
				union_iden = iden1;
			}
			else
			{
				parentMap.put(iden1, iden2);
				union_iden = iden2;
			}
		}
		return union_iden;
	}
	
	public HashMap<E, HashSet<E>> getSets()
	{
		HashMap<E, HashSet<E>> sets = new HashMap<E, HashSet<E>>();
		for(E element : parentMap.keySet())
		{
			E identifier = find(element);
			if(!sets.containsKey(identifier))
			{
				HashSet<E> set = new HashSet<E>();
				set.add(element);
				sets.put(identifier, set);
			}
			else
			{
				sets.get(identifier).add(element);
			}
		}
		return sets;
	}
	
	public String toString()
	{
		return getSets().toString();
	}
	
	
	
}
