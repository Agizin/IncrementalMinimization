import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.sat4j.specs.TimeoutException;

import com.google.common.base.Stopwatch;

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

public class TestIncrementalMinimization {

	//@Test
	public void testMyAut() throws TimeoutException {
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
				
		SFA<IntPred, Integer> incrMinAut = IncrementalMinimization.incrementalMinimize(aut, ba);
		SFA<IntPred, Integer> stdMinAut = aut.minimize(ba); //auts are equivalent but incrMin is not determinstic!
		Assert.assertTrue(incrMinAut.isDeterministic(ba));
		Assert.assertTrue(stdMinAut.isDeterministic(ba));
		Assert.assertTrue(incrMinAut.getStates().size() <= stdMinAut.getStates().size());
		Assert.assertTrue(SFA.areEquivalent(incrMinAut, aut, ba));
		Assert.assertTrue(SFA.areEquivalent(incrMinAut, stdMinAut, ba));
		
		//Note that because of how the symbolic automata library stores automata that it does not
		//recognize as explicitly minimal, we may have a case where our minimum automata has
		//less states than theirs (b/c the SFA does not store "sink states" AFAIK). So, to check that
		//our SFA is minimal, we test if it is deterministic and has no more than the minimum
		//SFA that the library computes
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
		transitions.add(new SFAInputMove<CharPred, Character>(0,0,a));
		CharPred lowerNotA = ba.MkAnd(alphaLower, ba.MkNot(a));
		transitions.add(new SFAInputMove<CharPred, Character>(0,1,lowerNotA));
		transitions.add(new SFAInputMove<CharPred, Character>(1,0,alphaLower));
		transitions.add(new SFAInputMove<CharPred, Character>(0,2,num));
		transitions.add(new SFAInputMove<CharPred, Character>(1,2,num));
		transitions.add(new SFAInputMove<CharPred, Character>(2,3,comma));
		transitions.add(new SFAInputMove<CharPred, Character>(3,4,alphaLower));
		transitions.add(new SFAInputMove<CharPred, Character>(3,1,num));
		transitions.add(new SFAInputMove<CharPred, Character>(4,3,lowerNotA));
		transitions.add(new SFAInputMove<CharPred, Character>(4,4,a));
		transitions.add(new SFAInputMove<CharPred, Character>(4,0,num));
		
		SFA<CharPred, Character> aut = SFA.MkSFA(transitions, 0, Arrays.asList(3,4), ba);
		aut = aut.determinize(ba).mkTotal(ba);
		
		SFA<CharPred, Character> incrMinAut = IncrementalMinimization.incrementalMinimize(aut, ba);
		SFA<CharPred, Character> stdMinAut = aut.minimize(ba);
		Assert.assertTrue(incrMinAut.isDeterministic(ba));
		Assert.assertTrue(SFA.areEquivalent(incrMinAut,stdMinAut,ba));
		Assert.assertTrue(incrMinAut.stateCount() <= stdMinAut.stateCount());
	}
	
	@Test
	public void testRegEx() throws TimeoutException, IOException
	{
		//import list of regex. Heavily borrowed code from symbolic automata library
		FileReader regexFile = new FileReader("src/pattern@75.txt");
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
		System.out.println(regexList.size());
		ArrayList<String> messageList = new ArrayList<String>();
		for (String regex : regexList)
		{
			SFA<CharPred, Character> aut = (new SFAprovider(regex, ba)).getSFA();
			if (aut.stateCount() > 200) //Disjoint Set data structure not optimized for large state space, TODO optimize
			{
				continue;
			}
			long incrStart = System.nanoTime();
			SFA<CharPred, Character> incrMinAut = IncrementalMinimization.incrementalMinimize(aut, ba);
			Double incrTime = ((double)(System.nanoTime() - incrStart)/1000);
			long stdStart = System.nanoTime();
			SFA<CharPred, Character> stdMinAut = aut.minimize(ba);
			Double stdTime = ((double)(System.nanoTime() - stdStart)/1000);
			Assert.assertTrue(incrMinAut.isDeterministic(ba));
			Assert.assertTrue(SFA.areEquivalent(incrMinAut, stdMinAut, ba));
			Assert.assertTrue(incrMinAut.stateCount() <= stdMinAut.stateCount());
			String initialStateCount = Integer.toString(aut.stateCount());
			String finalStateCount = Integer.toString(stdMinAut.stateCount());
			String message = "states: " + initialStateCount + " -> "  + finalStateCount + ", " 
					+ "incremental time: " + Double.toString(incrTime) + ", Standard time: " 
					+ Double.toString(stdTime) + " (microsecs)";
			messageList.add(message);
		}
		for (String msg : messageList)
		{
			System.out.println(msg);
		}
	}

}
