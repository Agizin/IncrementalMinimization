import org.sat4j.specs.TimeoutException;

import automata.sfa.SFA;

@SuppressWarnings("rawtypes") //throwable subclasses can not be made generic
public class TimeBudgetExceededException extends TimeoutException
{
	private final SFA returnAut;
	
	public TimeBudgetExceededException(String message, SFA returnAut)
	{
		super(message);
		this.returnAut = returnAut;
	}
	
	public TimeBudgetExceededException(SFA returnAut)
	{
		this("Time budget exceeded", returnAut);
	}

	public SFA getReturnAut()
	{
		return returnAut;
	}
}
