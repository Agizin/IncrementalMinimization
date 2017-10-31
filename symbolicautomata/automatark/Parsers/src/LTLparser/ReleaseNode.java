package LTLparser;

import java.io.*;

public class ReleaseNode extends BinaryLTLNode {
    public ReleaseNode(LTLNode l1, LTLNode l2) {
        super(l1, l2);
    }

    public void unparse(PrintWriter p, int indent) {
        p.print("(");
        myLTL1.unparse(p, 0);
        p.print(" R ");
        myLTL2.unparse(p, 0);
        p.print(")");
    }

	@Override
	public void toString(StringBuilder s, int indent) {
		s.append("(");
        myLTL1.toString(s, 0);
        s.append(" R ");
        myLTL2.toString(s, 0);
        s.append(")");
	}
}