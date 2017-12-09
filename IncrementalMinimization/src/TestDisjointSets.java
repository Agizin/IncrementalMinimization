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
		sets.union(3, 4);
		sets.union(2, 3);
		Assert.assertEquals(sets.find(1), sets.find(4));
		Assert.assertFalse(sets.find(1).equals(sets.find(5)));
	}

}
