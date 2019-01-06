bool b[2]				// Boolean array b(0;1) integer k, i, j

active [2] proctype p()			// comment process i
{	pid k, i = _pid, j = 1 -_pid	// with i either 0 or 1 and j = 1-i;

C0:	b[i] = false			// C0:	b(i) := false;
C1:	if
	:: k != i			// C1:	if k != i then begin
C2:	   if
	   :: !b[j] -> goto C2		// C2:	if not (b(j) then go to C2;
	   :: else -> k = i; goto C1	// else k := i; go to C1 end;
	   fi
	:: else
CS:	   skip				// else critical section;
	fi
	b[i] = true			// b(i) := true;
	skip				// remainder of program;
	goto C0				// go to C0;
}					// end

ltl invariant { [] (!p[0]@CS || !p[1]@CS)}
