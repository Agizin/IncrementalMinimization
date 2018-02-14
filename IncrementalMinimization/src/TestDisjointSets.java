import static org.junit.Assert.*;
import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;

public class TestDisjointSets {
	
	DisjointSets<Integer> sets;

	private void initialize()
	{
		sets = new DisjointSets<Integer>();
		for (Integer i = 0; i < 10; i++)
		{
			sets.make(i);
		}
	}

	@Test
	public void testFind()
	{
		initialize();
		for (Integer i = 0; i < 10; i++)
		{
			Assert.assertEquals(i, sets.find(i));
		}
	}
	
	@Test
	public void testUnion()
	{
		initialize();
		sets.union(new Integer(1), new Integer(2));
		Assert.assertEquals(sets.find(1), sets.find(2));
		Assert.assertEquals(new Integer(1),sets.find(1));
		Assert.assertEquals(new Integer(1),sets.find(2));
		sets.union(4, 5);
		sets.union(2, 4);
		Assert.assertEquals(sets.find(1), sets.find(5));
		Assert.assertFalse(sets.find(1).equals(sets.find(7)));
	}
	
	@Test
	public void testSize()
	{
		initialize();
		Assert.assertEquals(10, sets.size());
		sets.union(1, 2);
		Assert.assertEquals(9, sets.size());
		sets.union(4, 5);
		sets.union(2, 4);
		Assert.assertEquals(7, sets.size());
	}
	
	@Test
	public void testCopy()
	{
		initialize();
		sets.union(1, 2);
		sets.union(3, 4);
		sets.union(5, 4);
		DisjointSets<Integer> newSets = new DisjointSets<Integer>(sets);
		Integer oneIden = newSets.find(1);
		Assert.assertTrue(oneIden == 2 || oneIden == 1);
		Integer fiveIden = newSets.find(5);
		Assert.assertTrue(fiveIden == 3 || fiveIden == 4 || fiveIden == 5);
		for (Integer i = 6; i < 10; i++)
		{
			Assert.assertEquals(sets.find(i), newSets.find(i));
		}
	}

}
