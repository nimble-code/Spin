// http://spinroot.com/spin/Doc/Exercises.html
// faulty mutual exclusion algorithm

byte cnt
byte x, y, z

active [2] proctype user()
{	byte me = _pid+1			// 1 or 2

L1:	x = me
	if
	:: (y != 0 && y != me) -> goto L1	// try again
	:: (y == 0 || y == me)
	fi
	z = me
	if
	:: (x != me)  -> goto L1		// try again
	:: (x == me)
	fi
	y = me
	if
	:: (z != me) -> goto L1			// try again
	:: (z == me)
	fi					// success
	cnt++
	assert(cnt == 1)			// critical section
	cnt--
	goto L1
}
