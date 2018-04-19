package minimization.incremental;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.sat4j.specs.TimeoutException;

import structures.DependencyGraph;
import structures.DisjointSets;
import theory.BooleanAlgebra;
import automata.sfa.SFA;
import automata.sfa.SFAInputMove;

public class IncrWithDependencyChecks<P,S> extends IncrementalMinimization<P,S>
{

	protected class EquivTestDependency extends EquivTest //tests for equality of two given states in the automata
	{
		
		private DependencyGraph deps;
		
		public EquivTestDependency (DisjointSets<Integer> equivClasses, HashSet<List<Integer>> equiv, 
				HashSet<List<Integer>> path)
		{
			super(equivClasses, equiv, path);
			this.deps = new DependencyGraph();
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
				Collection<SFAInputMove<P,S>> outp = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(p));
				Collection<SFAInputMove<P,S>> outq = new ArrayList<SFAInputMove<P,S>>(aut.getInputMovesFrom(q));
				while(!outp.isEmpty() && !outq.isEmpty())
				{	
					HashSet<List<Integer>> newPath = new HashSet<List<Integer>>(curPath);
					newPath.add(pair);
					List<SFAInputMove<P,S>> nonDisjointGuards = findNonDisjointMoves(outp, outq);
					SFAInputMove<P,S> pMove = nonDisjointGuards.get(0);
					SFAInputMove<P,S> qMove = nonDisjointGuards.get(1);
					Integer pNextClass = equivClasses.find(pMove.to);
					Integer qNextClass = equivClasses.find(qMove.to);
					List<Integer> nextPair = normalize(pNextClass, qNextClass);
					if(equiv.contains(nextPair) || curPath.contains(nextPair))
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
							deps.mergeStates(equivClasses, newPath);
							this.path.clear();
							return false;
						}
						else
						{
							equiv.add(nextPair);
							EquivRecord nextTest = new EquivRecord(pNextClass, qNextClass, newPath);
							testStack.add(nextTest);
							deps.addDependency(pair, nextPair);
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
