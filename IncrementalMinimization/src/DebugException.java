
class DebugException extends Exception
{
	private final Integer maxDepth;
			
	public DebugException (String message, Integer maxDepth)
	{
		super(message);
		this.maxDepth = maxDepth;
	}
	
	public DebugException (String message)
	{
		this(message, null);
	}
			
	public int getDepth()
	{
		return maxDepth;
	}
}