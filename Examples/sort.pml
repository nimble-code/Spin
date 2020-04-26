/*
 * A program to sort concurrently N "random" numbers
 * The reduced space and time should be linear in the
 * number of processes, and can be reduced when the length of
 * the buffer queues is increased.
 * In full search it should be exponential.
 */

#define N	7			/* Number of Proc */
#define L	10			/* Size of buffer queues */
#define RANDOM	(seed * 3 + 14) % 100	/* Calculate "random" number */

chan q[N] = [L] of {byte};

proctype left(chan out)			/* leftmost process, generates random numbers */
{	byte counter, seed;

	xs out;

	counter = 0; seed = 15;
	do
	:: out!seed ->			/* output value to the right */
		counter = counter + 1;
		if
		:: counter == N -> break
		:: counter != N -> skip
		fi;
		seed = RANDOM		/* next "random" number */
	od
}

proctype middle(chan inp, out; byte procnum)
{	byte counter, myval, nextval;

	xs out;
	xr inp;

	counter = N - procnum;
	inp?myval;				/* get first value from the left */
	do
	:: counter > 0 ->
		inp?nextval;			/* upon receipt of a new value */
		if
		:: nextval >= myval -> out!nextval
		:: nextval <  myval ->
			out!myval;
			myval=nextval		/* send bigger, hold smaller */
		fi;
		counter = counter - 1
	:: counter == 0 -> break
	od
}

proctype right(chan inp)	/* rightmost channel */
{	byte biggest;

	xr inp;

	inp?biggest		/* accepts only one value, which is the biggest */
}

init {
	byte proc=1;

	atomic {
		run left ( q[0] );
		do
		:: proc < N ->
			run middle ( q[proc-1] , q[proc], proc );
			proc = proc+1
		:: proc == N -> break
		od;
		run right ( q[N-1] )
	}
}

