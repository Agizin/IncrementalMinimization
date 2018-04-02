package minimization;

import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;

public interface MinimizationAlgorithm <P,S>
{
	public SFA<P,S> minimize() throws TimeoutException, DebugException;
}
