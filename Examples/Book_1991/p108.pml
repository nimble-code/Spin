/***** Ackermann's function *****/

/*	a good example where a simulation run is the
	better choice - and verification is overkill.

	1. simulation
		-> straight simulation (spin p108) takes
		-> approx. 6.4 sec on an SGI R3000
		-> prints the answer: ack(3,3) = 61
		-> after creating 2433 processes

	note: all process invocations can, at least in one
	feasible execution scenario, overlap - if each
	process chooses to hang around indefinitely in
	its dying state, at the closing curly brace.
	this means that the maximum state vector `could' grow
	to hold all 2433 processes or about 2433*12 bytes of data.
	the assert(0) at the end makes sure though that the run
	stops the first time we complete an execution sequence
	that computes the answer, so the following suffices:

	2. verification
		-> spin -a p108
		-> cc -DVECTORSZ=2048 -o pan pan.c
		-> pan -m15000
		-> which completes in about 5 sec
 */

proctype ack(short a, b; chan ch1)
{	chan ch2 = [1] of { short };
	short ans;

	if
	:: (a == 0) ->
		ans = b+1
	:: (a != 0) ->
		if
		:: (b == 0) ->
			run ack(a-1, 1, ch2)
		:: (b != 0) ->
			run ack(a, b-1, ch2);
			ch2?ans;
			run ack(a-1, ans, ch2)
		fi;
		ch2?ans
	fi;
	ch1!ans
}
init
{	chan ch = [1] of { short };
	short ans;

	run ack(3, 3, ch);
	ch?ans;
	printf("ack(3,3) = %d\n", ans);
	assert(0)	/* a forced stop, (Chapter 6) */
}
