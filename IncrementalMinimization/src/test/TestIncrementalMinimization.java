package test;
import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;


import minimization.DebugException;
import minimization.MooreMinimization;
import minimization.incremental.IncrementalMinimization;
import minimization.incremental.IncrementalNaive;
import minimization.incremental.IncrementalRecursive;
import minimization.incremental.TimeBudgetExceededException;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import benchmark.SFAprovider;

import theory.BooleanAlgebra;
import theory.characters.CharPred;
import theory.characters.StdCharPred;
import theory.intervals.IntPred;
import theory.intervals.IntegerSolver;
import theory.intervals.UnaryCharIntervalSolver;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;
import automata.sfa.SFAMove;

public class TestIncrementalMinimization 
{
	public static final String REGEX_FILE = "src/test/regexlib-SFA.txt";

	@Test
	public void testMyAut() throws TimeoutException
	{
		//our algebra is constructed
		IntegerSolver ba = new IntegerSolver();
		IntPred neg = new IntPred(null, new Integer(0));
		IntPred less_neg_ten = new IntPred(null, new Integer(-10));
		IntPred great_pos_ten = new IntPred(new Integer(10), null);
		IntPred zero = new IntPred(new Integer(0));
		IntPred one = new IntPred(1);
		IntPred zero_five = new IntPred(new Integer(0), new Integer(5));
		IntPred pos = new IntPred(new Integer(1), null);
				
		//transitions are defined
		Collection <SFAMove<IntPred,Integer>> transitions = new LinkedList<SFAMove<IntPred, Integer>>();
		IntPred a_pred = ba.MkAnd(ba.MkNot(one), ba.MkNot(zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,0,a_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,1,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(0,2,one));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,0,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,1,a_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(1,2,one));
		IntPred b_pred = ba.MkAnd(pos, ba.MkNot(zero_five));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,2,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,3,neg));
		IntPred c_pred = ba.MkAnd(ba.MkNot(zero), zero_five);
		transitions.add(new SFAInputMove<IntPred, Integer>(2,5,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(2,6,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(3,3,ba.True()));
		transitions.add(new SFAInputMove<IntPred, Integer>(4,4,ba.True()));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,3, neg));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,3,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,6,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(5,7,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,4,neg));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,4,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,5,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(6,7,b_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,1,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,4,ba.MkNot(c_pred)));
		transitions.add(new SFAInputMove<IntPred, Integer>(7,8,c_pred));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,0,zero));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,3,ba.MkNot(c_pred)));
		transitions.add(new SFAInputMove<IntPred, Integer>(8,7,c_pred));
				
		//SFA is defined
		SFA<IntPred, Integer> aut = SFA.MkSFA(transitions, 0, Arrays.asList(7,8), ba);
				
		IncrementalMinimization<IntPred, Integer> incr = new IncrementalMinimization<IntPred, Integer>(aut,ba);
		SFA<IntPred, Integer> incrMinAut = incr.minimize();
		SFA<IntPred, Integer> stdMinAut = aut.minimize(ba); //auts are equivalent but incrMin is not determinstic!
		IncrementalNaive<IntPred, Integer> naive = new IncrementalNaive<IntPred, Integer>(aut,ba);
		SFA<IntPred, Integer> upfrontMinAut = naive.minimize();
		
		Assert.assertTrue(incrMinAut.isDeterministic(ba));
		Assert.assertTrue(stdMinAut.isDeterministic(ba));
		Assert.assertTrue(upfrontMinAut.isDeterministic(ba));
		Assert.assertTrue(incrMinAut.getStates().size() <= stdMinAut.getStates().size());
		Assert.assertTrue(upfrontMinAut.getStates().size() <= stdMinAut.getStates().size());
		Assert.assertTrue(SFA.areEquivalent(incrMinAut, aut, ba));
		Assert.assertTrue(SFA.areEquivalent(incrMinAut, stdMinAut, ba));
		Assert.assertTrue(SFA.areEquivalent(upfrontMinAut, stdMinAut, ba));
	}
	
	@Test
	public void testCharPred() throws TimeoutException
	{
		UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
		CharPred alphaLower = StdCharPred.LOWER_ALPHA;
		CharPred alphaAll = StdCharPred.ALPHA;
		CharPred a = new CharPred('a');
		CharPred num = StdCharPred.NUM;
		CharPred comma = new CharPred(',');
		
		Collection<SFAMove<CharPred, Character>> transitions = new LinkedList<SFAMove<CharPred, Character>>();
		transitions.add(new SFAInputMove<CharPred, Character>(9,9,a));
		CharPred lowerNotA = ba.MkAnd(alphaLower, ba.MkNot(a));
		transitions.add(new SFAInputMove<CharPred, Character>(9,1,lowerNotA));
		transitions.add(new SFAInputMove<CharPred, Character>(1,9,alphaLower));
		transitions.add(new SFAInputMove<CharPred, Character>(9,2,num));
		transitions.add(new SFAInputMove<CharPred, Character>(1,2,num));
		transitions.add(new SFAInputMove<CharPred, Character>(2,3,comma));
		transitions.add(new SFAInputMove<CharPred, Character>(3,4,alphaLower));
		transitions.add(new SFAInputMove<CharPred, Character>(3,1,num));
		transitions.add(new SFAInputMove<CharPred, Character>(4,3,lowerNotA));
		transitions.add(new SFAInputMove<CharPred, Character>(4,4,a));
		transitions.add(new SFAInputMove<CharPred, Character>(4,9,num));
		
		SFA<CharPred, Character> aut = SFA.MkSFA(transitions, 9, Arrays.asList(3,4), ba);
		aut = aut.determinize(ba).mkTotal(ba);
		
		IncrementalMinimization<CharPred, Character> incr = new IncrementalMinimization<CharPred, Character>(aut,ba);
		SFA<CharPred, Character> incrMinAut = incr.minimize();
		System.out.println(incrMinAut.getStates());
		SFA<CharPred, Character> stdMinAut = aut.minimize(ba);
		System.out.println(stdMinAut.getStates());
		Assert.assertTrue(incrMinAut.isDeterministic(ba));
		Assert.assertTrue(SFA.areEquivalent(incrMinAut,stdMinAut,ba));
		Assert.assertTrue(incrMinAut.stateCount() <= stdMinAut.stateCount());
	}
	
	@Test
	public void testCompare() throws TimeoutException, IOException
	{
		System.out.println("========================");
		System.out.println("STARTING COMPARISON TEST");
		System.out.println("========================");
		
		//import list of regex. Heavily borrowed code from symbolic automata library
		FileReader regexFile = new FileReader(REGEX_FILE);
		BufferedReader read = new BufferedReader(regexFile);
		ArrayList<String> regexList = new ArrayList<String>();
		String line;
		while(true)
		{
			line = read.readLine();
			if (line == null)
			{
				break;
			}
			regexList.add(line);
		}
		//regex converted to SFAs and minimized
		UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
		//System.out.println(regexList.size());
		ArrayList<String> messageList = new ArrayList<String>();
		long timeout = 3600000; //determinization timeout = 1 hour
		for (String regex : regexList)
		{
			SFA<CharPred, Character> aut = (new SFAprovider(regex, ba)).getSFA();
			try
			{
				aut = aut.determinize(ba, timeout);
				aut = aut.mkTotal(ba);
			}
			catch(TimeoutException e)
			{
				continue;
			}
			catch(OutOfMemoryError e)
			{
				System.gc();
				continue;
			}
			System.out.println("Determinized");
			
			//standard minimization
			long stdStart = System.nanoTime();
			SFA<CharPred, Character> stdMinAut;
			stdMinAut = aut.minimize(ba);
			Double stdTime = ((double)(System.nanoTime() - stdStart)/1000000);
			System.out.println("Standard minimized.");
			
			//moore minimization
			long mooreStart = System.nanoTime();
			SFA<CharPred, Character> mooreMinAut;
			mooreMinAut = MooreMinimization.mooreMinimize(aut, ba);
			Double mooreTime = ((double)(System.nanoTime() - mooreStart)/1000000);
			Assert.assertTrue(SFA.areEquivalent(mooreMinAut, stdMinAut, ba));
			Assert.assertTrue(mooreMinAut.stateCount() <= stdMinAut.stateCount());
			System.out.println("Moore minimized.");
			
			//incremental minimization
			System.out.println("Starting incremental minimization");
			long incrStart = System.nanoTime();
			SFA<CharPred, Character> incrMinAut;
			try
			{
				IncrementalMinimization<CharPred,Character> incrMin = new IncrementalMinimization<CharPred,Character>(aut, ba);
				incrMinAut = incrMin.minimize();
			}
			catch(TimeoutException e)
			{
				System.out.println("Skipping because of Timeout Exception"); //TODO Debug
				continue;
			}
			/*catch(OutOfMemoryError e)
			{
				System.out.println("Skipping because out of heap space"); //TODO Debug
				continue;
			}*/
			Double incrTime = ((double)(System.nanoTime() - incrStart)/1000000);
			Assert.assertTrue(incrMinAut.isDeterministic(ba));
			Assert.assertTrue(SFA.areEquivalent(incrMinAut, stdMinAut, ba));
			Assert.assertTrue(incrMinAut.stateCount() <= stdMinAut.stateCount());
			System.out.println("Incremental minimized.");
			
			
			//DFAized incremental minimization
			System.out.println("Starting upfront incremental");
			long incrDFAStart = System.nanoTime();
			SFA<CharPred, Character> upfrontMinAut;
			try
			{
				IncrementalNaive<CharPred,Character> naiveMin = new IncrementalNaive<CharPred,Character>(aut, ba);
				upfrontMinAut = naiveMin.minimize();
			}
			catch(TimeoutException e)
			{
				System.out.println("Skipping because of Timeout Exception"); //TODO Debug
				continue;
			}
			/*catch(OutOfMemoryError e)
			{
				System.out.println("Skipping because out of heap space"); //TODO Debug
				continue;
			}*/
			Double upfrontTime = ((double)(System.nanoTime() - incrDFAStart)/1000000);
			Assert.assertTrue(upfrontMinAut.stateCount() <= stdMinAut.stateCount());
			Assert.assertTrue(SFA.areEquivalent(upfrontMinAut, stdMinAut, ba));
			Assert.assertEquals(upfrontMinAut.stateCount(), incrMinAut.stateCount());
			/*try
			{
				Assert.assertTrue(upfrontMinAut.stateCount() == incrMinAut.stateCount());
			}
			catch(AssertionError e)
			{
				System.out.println(upfrontMinAut.stateCount());
				System.out.println(incrMinAut.stateCount());
				throw(e);
			}*/
			Assert.assertTrue(SFA.areEquivalent(upfrontMinAut, stdMinAut, ba));
			System.out.println("Upfront Incremental minimized.");
			
			//recursive incremental
			System.out.println("Starting Recursive incremental w/ dependency check");
			long recStart = System.nanoTime();
			SFA<CharPred, Character> recursiveMinAut;
			try
			{
				IncrementalRecursive<CharPred,Character> incrRec = new IncrementalRecursive<CharPred,Character>(aut, ba);
				recursiveMinAut = incrRec.minimize();
			}
			catch(TimeoutException e)
			{
				System.out.println("Skipping because of Timeout Exception"); //TODO: does this come up?
				continue;
			}
			Double recTime = ((double)(System.nanoTime() - recStart)/1000000);
			Assert.assertTrue(recursiveMinAut.stateCount() <= stdMinAut.stateCount());
			try
			{
				Assert.assertTrue(SFA.areEquivalent(recursiveMinAut, stdMinAut, ba));
			}
			catch(AssertionError e)
			{
				System.out.println(recursiveMinAut);
				System.out.println(stdMinAut);
				throw e;
			}
			Assert.assertTrue(SFA.areEquivalent(recursiveMinAut, incrMinAut, ba));
			Assert.assertEquals(recursiveMinAut.stateCount(), incrMinAut.stateCount());
			
			//standard incremental w/ dependency check
			System.out.println("Starting standard incremental w/ dependency check");
			long depStart = System.nanoTime();
			SFA<CharPred, Character> depMinAut;
			try
			{
				IncrementalRecursive<CharPred,Character> incrDep = new IncrementalRecursive<CharPred,Character>(aut, ba);
				depMinAut = incrDep.minimize();
			}
			catch(TimeoutException e)
			{
				System.out.println("Skipping because of Timeout Exception"); //TODO: does this come up?
				continue;
			}
			Double depTime = ((double)(System.nanoTime() - depStart)/1000000);
			Assert.assertTrue(depMinAut.stateCount() <= stdMinAut.stateCount());
			try
			{
				Assert.assertTrue(SFA.areEquivalent(depMinAut, stdMinAut, ba));
			}
			catch(AssertionError e)
			{
				System.out.println(recursiveMinAut);
				System.out.println(stdMinAut);
				throw e;
			}
			Assert.assertTrue(SFA.areEquivalent(depMinAut, incrMinAut, ba));
			Assert.assertEquals(depMinAut.stateCount(), incrMinAut.stateCount());
	
			String initialStateCount = Integer.toString(aut.stateCount());
			String transCount = Integer.toString(aut.getTransitionCount());
			String finalStateCount = Integer.toString(stdMinAut.stateCount());
			
			HashSet<CharPred> predSet = new HashSet<CharPred>();
			for(SFAInputMove<CharPred, Character> t : aut.getInputMovesFrom(aut.getStates()))
			{
				predSet.add(t.guard);
			}
			String predCount = Integer.toString(predSet.size());
			ArrayList<CharPred> predList = new ArrayList<CharPred>(predSet);
			String mintermCount = Integer.toString(ba.GetMinterms(predList).size());
			
			String message = String.format("%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s",
					initialStateCount, finalStateCount, transCount, predCount, mintermCount,
					Double.toString(incrTime), Double.toString(stdTime), Double.toString(mooreTime),
					Double.toString(upfrontTime), Double.toString(recTime), Double.toString(depTime));
			System.out.println(message);
			messageList.add(message);
		}
		FileOutputStream file = new FileOutputStream("compare_test.txt");
		Writer writer = new BufferedWriter(new OutputStreamWriter(file));
		writer.write("initial states, final states, transition count, predicate count, minterm count," +
				"incremental time, standard time, Moore time, upfront incremental time, " +
				"recursive symbolic incremental, With Dependency check \n");
		for (String msg : messageList)
		{
			writer.write(msg + "\n");
		}
		writer.close();
	}
	
	//@Test
	public void testBudget() throws TimeoutException, IOException
	{
		//Similar to Regex test, but incremental minimization only given as long as 
		
		System.out.println("=========================");
		System.out.println("STARTING TIME BUDGET TEST");
		System.out.println("=========================");
		
		//import list of regex
		FileReader regexFile = new FileReader(REGEX_FILE);
		BufferedReader read = new BufferedReader(regexFile);
		ArrayList<String> regexList = new ArrayList<String>();
		String line;
		while(true)
		{
			line = read.readLine();
			if (line == null)
			{
				break;
			}
			regexList.add(line);
		}
		//regex converted to SFAs and minimized
		UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
		ArrayList<String> messageList = new ArrayList<String>();
		long timeout = 3600000; //determinization timeout = 1 hour
		for(String regex : regexList)
		{
			SFA<CharPred, Character> aut = (new SFAprovider(regex, ba)).getSFA();
			try
			{
				aut = aut.determinize(ba, timeout);
				aut = aut.mkTotal(ba);
			}
			catch(TimeoutException e)
			{
				continue;
			}
			catch(OutOfMemoryError e)
			{
				System.gc();
				continue;
			}
			System.out.println("Determinized.");
			
			//Standard minimiazation runs first
			long stdStart = System.nanoTime();
			SFA<CharPred, Character> stdMinAut;
			long budget;
			try
			{
				stdMinAut = aut.minimize(ba);
				budget = System.nanoTime() - stdStart;
			}
			catch(TimeoutException e)
			{
				continue;
			}
			double bms = (new Double(budget))/1000000;
			System.out.println(String.format("Standard minimization computed, budget: %f ms", bms));
			
			//Incremental minimization runs with time budget of standard minimization
			SFA<CharPred, Character> incrMinAut;
			SFA<CharPred, Character> upfrontIncrAut;
			try
			{
				IncrementalMinimization<CharPred, Character> incrMin = new IncrementalMinimization<CharPred, Character>(aut,ba);
				incrMinAut = incrMin.minimize(budget);
			}
			catch(TimeBudgetExceededException e)
			{
				incrMinAut = e.getReturnAut();
			}
			catch(TimeoutException e)
			{
				continue;
			}
			System.out.println("Incremental minimized.");
			try
			{
				IncrementalNaive<CharPred,Character> naiveMin = new IncrementalNaive<CharPred,Character>(aut, ba);
				upfrontIncrAut = naiveMin.minimize(budget);
			}
			catch(TimeBudgetExceededException e)
			{
				upfrontIncrAut = e.getReturnAut();
			}
			catch(TimeoutException e)
			{
				continue;
			}
			/*catch(OutOfMemoryError e)
			{
				continue;
			}*/
			System.out.println("Naive incremental minimized..");
			
			int initialCount = aut.stateCount();
			String initialStateCount = Integer.toString(initialCount);
			int finalCount = stdMinAut.stateCount();
			String finalStateCount =  Integer.toString(finalCount);
			int incrCount = incrMinAut.stateCount();
			String incrStateCount= Integer.toString(incrCount);
			int upfrontCount = upfrontIncrAut.stateCount();
			String upfrontStateCount = Integer.toString(upfrontCount);
					
			double incrPercentMinimized;
			if (incrCount <= finalCount)
			{
				incrPercentMinimized = 1.;
			}
			else
			{
				incrPercentMinimized = ((double) initialCount - incrCount)/((double) initialCount - finalCount);
			}
			String incrPercent = Double.toString(incrPercentMinimized);
			double upfPercentMinimized;
			if (upfrontCount <= finalCount)
			{
				upfPercentMinimized = 1.;
			}
			else
			{
				upfPercentMinimized = ((double) initialCount - upfrontCount)/((double)initialCount - finalCount);
			}
			String upfPercent = Double.toString(upfPercentMinimized);
			
			String msg = String.format("%s, %s, %s, %s, %s, %s", 
					initialStateCount, finalStateCount, incrStateCount, upfrontCount, 
					incrPercent, upfPercent);
			messageList.add(msg);
			System.out.println(msg);
			Assert.assertTrue(incrPercentMinimized >= 0);
		}
		FileOutputStream file = new FileOutputStream("budget_test.txt");
		Writer writer = new BufferedWriter(new OutputStreamWriter(file));
		writer.write("initial states, final states, incremental states, upfront states" +
				"incremental percent, upfront percent" + "\n");
		for (String msg : messageList)
		{
			writer.write(msg + "\n");
		}
		writer.close();
	}
	
	private Double getTimePercentage(Double currentTime, Double startTime, Double finishTime)
	{
		Assert.assertTrue(finishTime >= currentTime);
		Double relativeTime = ((currentTime - startTime)/(finishTime - startTime))*100.0;
		Assert.assertTrue(relativeTime >= 0);
		Assert.assertTrue(relativeTime <= 100);
		return relativeTime;
	}
	
	private Double getMinimizedPercentage(Double curCount, Double initialCount, Double finalCount)
	{
		Assert.assertTrue(curCount <= initialCount);
		Assert.assertTrue(finalCount <= curCount);
		Double percentage = ((initialCount - curCount)/(initialCount - finalCount))*100.0;
		Assert.assertTrue(percentage >= 0);
		Assert.assertTrue(percentage <= 100);
		return percentage;
	}
	
	private Double linearInterpolate(Integer x, Integer x0, Integer x1, Double y0, Double y1)
	{
		Double slope = (y1-y0)/(x1-x0);
		return y0 + (x-x0)*slope;
	}
	
	//@Test
	public void testRecord() throws IOException
	{
		//TODO: cleanup + document
		System.out.println("====================");
		System.out.println("STARTING RECORD TEST");
		System.out.println("====================");
		
		//import list of regex
		FileReader regexFile = new FileReader(REGEX_FILE);
		BufferedReader read = new BufferedReader(regexFile);
		ArrayList<String> regexList = new ArrayList<String>();
		String line;
		while(true)
		{
			line = read.readLine();
			if (line == null)
			{
				break;
			}
			regexList.add(line);
		}
		//regex converted to SFAs and minimized
		UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
		ArrayList<String> messageList = new ArrayList<String>();
		long timeout = 3600000; //determinization timeout = 1 hour
		
		Integer[] milestones = new Integer[101];
		for(int i = 0; i < milestones.length; i++)
		{
			milestones[i] = i;
		}
		TreeMap<Integer, HashMap<Integer, Double>> fullMinimizationMap = new TreeMap<Integer, HashMap<Integer, Double>>();
		TreeMap<Integer, HashMap<Integer, Double>> oppositeMap = new TreeMap<Integer, HashMap<Integer, Double>>();
		HashMap<Integer, Double> repeatCount = new HashMap<Integer, Double>();
		HashMap<Integer, Double> otherRepeat = new HashMap<Integer, Double>();
		for(String regex : regexList)
		{
			SFA<CharPred, Character> aut = (new SFAprovider(regex, ba)).getSFA();
			try
			{
				aut = aut.determinize(ba, timeout);
				aut = aut.mkTotal(ba);
			}
			catch(TimeoutException e)
			{
				continue;
			}
			catch(OutOfMemoryError e)
			{
				System.gc();
				continue;
			}
			if(aut.stateCount() > 400 || aut.stateCount() <= 1)
			{
				continue;
			}
			System.out.println("Determinized.");
			
			SFA<CharPred, Character> incrMinAut =null;
			LinkedHashMap<Long, Integer> record = null;
			try
			{
				IncrementalMinimization<CharPred,Character> incrMin = 
						new IncrementalMinimization<CharPred, Character>(aut, ba);
				incrMinAut = incrMin.minimize(Long.MAX_VALUE, true, false);
				record = incrMin.getRecord();
			}
			catch(TimeoutException e)
			{
				continue;
			}
			catch(DebugException e)
			{
				//This will never occur
				Assert.fail();
			}
			/*catch(OutOfMemoryError e)
			{
				continue;
			}*/
			Assert.assertTrue(incrMinAut != null);
			Assert.assertTrue(record != null);
			System.out.println("Minimized.");
			if(record.size()<=1)
			{
				continue;
			}
			Iterator<Long> timeIter = record.keySet().iterator();
			Long startTime = timeIter.next();
			Long finalTime = startTime;
			while (timeIter.hasNext())
			{
				finalTime = timeIter.next();
			}
			Integer finalStateCount = record.get(finalTime);
			Assert.assertEquals(incrMinAut.stateCount(), finalStateCount);
			Integer initialStateCount = aut.stateCount();
			if(finalStateCount == initialStateCount)
			{
				continue;
			}
			HashMap<Integer, Double> minimizationTimes = new LinkedHashMap<Integer, Double>();
			HashMap<Integer, Double> minimizationPercents = new LinkedHashMap<Integer, Double>();
			minimizationTimes.put(0, 0.0);
			minimizationPercents.put(0, 0.0);
			int milestoneIndex = 0;
			int otherIndex = 0; //TODO: fix literally all of these variable names - make readable!
			for (Long time : record.keySet())
			{
				Double timePercent = getTimePercentage((double)time, (double)startTime, (double)finalTime);
				Integer stateCount = record.get(time);
				Double percentMinimized = getMinimizedPercentage((double)stateCount, (double) initialStateCount, (double) finalStateCount);
				Integer currentMilestone = milestones[milestoneIndex];
				if (timePercent <= currentMilestone)
				{
					if (minimizationTimes.containsKey(currentMilestone))
					{
						Assert.assertTrue(percentMinimized >= minimizationTimes.get(currentMilestone));
					}
					minimizationTimes.put(currentMilestone, percentMinimized);
				}
				else
				{
					while(timePercent > currentMilestone)
					{
						Double prevMilestonePercent = minimizationTimes.get(currentMilestone);
						milestoneIndex++;
						currentMilestone = milestones[milestoneIndex];
						minimizationTimes.put(currentMilestone, prevMilestonePercent);
						Assert.assertTrue(prevMilestonePercent <= percentMinimized);
					}
					minimizationTimes.put(currentMilestone, percentMinimized);
				}
				Double msTime = (new Double(time))/1000000.0;
				currentMilestone = milestones[otherIndex];
				if (percentMinimized <= currentMilestone)
				{
					if (minimizationPercents.containsKey(currentMilestone))
					{
						Assert.assertTrue(msTime >= minimizationPercents.get(currentMilestone));
					}
					minimizationPercents.put(currentMilestone, msTime);
				}
				else
				{	
					Double prevMilestoneTime = minimizationPercents.get(currentMilestone);
					Integer startIndex = new Integer(otherIndex);
					while(percentMinimized > currentMilestone)
					{
						otherIndex++;
						currentMilestone = milestones[otherIndex]; //actually not for time anymore...
					}
					Assert.assertTrue(startIndex < otherIndex);
					Integer curIndex = new Integer(startIndex + 1);
					if(curIndex == otherIndex)
					{
						minimizationPercents.put(currentMilestone, msTime);
					}
					else
					{
						Integer prevMilestone = milestones[startIndex];
						while(curIndex < otherIndex)
						{
							Integer skippedMilestone = milestones[curIndex];
							minimizationPercents.put(skippedMilestone,
									linearInterpolate(skippedMilestone, prevMilestone, currentMilestone, prevMilestoneTime, msTime));
							curIndex++;
						}
						minimizationPercents.put(currentMilestone, msTime);
					}
				}
			}
			if (!fullMinimizationMap.containsKey(initialStateCount))
			{
				repeatCount.put(initialStateCount, 1.0);
				fullMinimizationMap.put(initialStateCount, minimizationTimes);
			}
			else
			{
				Double count = repeatCount.get(initialStateCount);
				HashMap<Integer, Double> avgMinTimes = fullMinimizationMap.get(initialStateCount);
				for(Integer milestone : avgMinTimes.keySet())
				{
					Double curMilestonePercent = minimizationTimes.get(milestone);
					Double avgMilestonePercent = avgMinTimes.get(milestone);
					Double newAvg = avgMilestonePercent + (curMilestonePercent - avgMilestonePercent)/count;
					avgMinTimes.put(milestone, newAvg);
				}
				repeatCount.put(initialStateCount, count+1);
			}
			if (!oppositeMap.containsKey(initialStateCount))
			{
				otherRepeat.put(initialStateCount, 1.0);
				oppositeMap.put(initialStateCount, minimizationPercents);
			}
			else
			{
				Double count = otherRepeat.get(initialStateCount);
				HashMap<Integer, Double> avgMinPercents = oppositeMap.get(initialStateCount);
				for (Integer milestone : avgMinPercents.keySet())
				{
					Double curMilestoneTime = minimizationPercents.get(milestone);
					Double avgMilestoneTime = avgMinPercents.get(milestone);
					Double newAvg = avgMilestoneTime + (curMilestoneTime - avgMilestoneTime)/count;
					avgMinPercents.put(milestone, newAvg);
				}
				otherRepeat.put(initialStateCount, count+1);
			}
		}
		String titleRow = "initial states, ";
		for (Integer milestone : milestones)
		{
			titleRow += String.format("%d, ", milestone);
		}
		titleRow += "\n";
		System.out.print(titleRow);
		FileOutputStream file = new FileOutputStream("second_record_test.txt");
		Writer writer = new BufferedWriter(new OutputStreamWriter(file));
		writer.write(titleRow);
		for(Integer stateCount : oppositeMap.keySet())
		{
			HashMap<Integer, Double> minTimes = oppositeMap.get(stateCount);
			String row = String.format("%d, ", stateCount);
			for (Integer milestone : milestones)
			{
				Double timeMin = minTimes.get(milestone);
				row += String.format("%f, ", timeMin);
			}
			row += "\n";
			System.out.print(row);
			writer.write(row);
		}
		writer.close();
	}
	
	//@Test
	public void testDepth() throws IOException, TimeoutException
	{
		System.out.println("===================");
		System.out.println("STARTING DEPTH TEST");
		System.out.println("===================");
		//import list of regex
		FileReader regexFile = new FileReader(REGEX_FILE);
		BufferedReader read = new BufferedReader(regexFile);
		ArrayList<String> regexList = new ArrayList<String>();
		String line;
		while(true)
		{
			line = read.readLine();
			if (line == null)
			{
				break;
			}
			regexList.add(line);
		}
		//regex converted to SFAs and minimized
		UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
		ArrayList<String> messageList = new ArrayList<String>();
		long timeout = 3600000; //determinization timeout = 1 hour
		
		double sumOfAvgs = 0;
		double lengthOfAvgs = 0;
		
		regexLoop: //labels to break out from nested loops
		for(String regex : regexList)
		{
			SFA<CharPred, Character> aut = (new SFAprovider(regex, ba)).getSFA();
			try
			{
				aut = aut.determinize(ba, timeout);
				aut = aut.mkTotal(ba);
			}
			catch(TimeoutException e)
			{
				continue;
			}
			catch(OutOfMemoryError e)
			{
				System.gc();
				continue;
			}
			System.out.println("Determinized.");
			
			int tests = 5; //We do 5 tests per regex
			int depthSum = 0;
			for (int i = 0; i < tests; i++)
			{
				IncrementalMinimization<CharPred, Character> dbgTest = new IncrementalMinimization(aut, ba);
				Integer maxDepth = null;
				SFA<CharPred, Character> minAut = null;
				try
				{
					minAut = dbgTest.minimize(Long.MAX_VALUE, false, true);
				}
				catch (DebugException e)
				{
					maxDepth = e.getDepth();
				}
				if (maxDepth == null)
				{
					Assert.assertEquals(aut.stateCount(), minAut.stateCount());
					continue regexLoop;
				}
				
				depthSum += maxDepth;
			}
			int startSize = aut.stateCount();
			double depthAvg = depthSum / (new Double(tests));
			sumOfAvgs += depthAvg;
			lengthOfAvgs += 1;
			double percSize = (startSize-depthAvg)/(new Double(startSize));
			String row = String.format("%d, %f, %f", startSize, depthAvg, percSize);
			messageList.add(row);
			System.out.println(row);
		}
		System.out.println(String.format("Average: %f", sumOfAvgs/lengthOfAvgs));
		String titlerow = "states, depth, percent \n";
		FileOutputStream file = new FileOutputStream("depth_test.txt");
		Writer writer = new BufferedWriter(new OutputStreamWriter(file));
		writer.write(titlerow);
		for (String msg : messageList)
		{
			writer.write(msg + "\n");
		}
		writer.close();
		
	}

}
