import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;


public class DisjointSets <E>
{
	//TODO: rewrite or find an implementation using "rooted trees" for optimization
	
	//naive implementation inspired from http://www.cs.cornell.edu/~wdtseng/icpc/notes/graph_part4.pdf
	//parentMap contains a forest of implicit trees with the identifiers of the sets at the root, every element in parentMap is mapped to its parent in its tree
	 
	private HashMap<E, E> parentMap;
	
	public DisjointSets()
	{
		parentMap = new HashMap<E, E>();
	}
	
	public DisjointSets(Collection<E> identifiers)
	{
		parentMap = new HashMap<E, E>();
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
		}
		else
		{
			throw new IllegalArgumentException("Identifier already exists in a set");
		}
	}
	
	public E find(E element) throws IllegalArgumentException
	{
		if(parentMap.containsKey(element))
		{
			E parent = parentMap.get(element);
			if(parent == null)
			{
				return element;
			}
			else
			{
				return find(parent);
			}
		}
		else
		{
			throw new IllegalArgumentException("Element not found in any disjoint set");
		}
	}
	
	public E union(E elem1, E elem2)
	{
		E iden1 = find(elem1);
		E iden2 = find(elem2);
		E union_iden;
		if(iden1 == iden2)
		{
			union_iden = iden1;
		}
		else
		{
			try //if E extends comparable, the lesser element will always be new identifier
			{
				if (((Comparable) iden1).compareTo((Comparable) iden2) <= 0)
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
			catch(Exception e)
			{
				parentMap.put(iden2, iden1);
				union_iden = iden1;
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
