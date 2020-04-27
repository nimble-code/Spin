/* Lamport's Bakery algorithm for 2 processes */

byte turn[2];  /* who's turn is it?           */
byte mutex;    /* # procs in critical section */

active [2] proctype P()
{	byte i = _pid;
	do
	:: turn[i] = 1;
		turn[i] = turn[1-i] + 1;
		(turn[1-i] == 0) || (turn[i] < turn[1-i]) ->
		mutex++;
CS:		/* critical section */
		mutex--;
		turn[i] = 0
	od
}

/*
 * place the ltl property goes at the end,
 * so that P and mutex are defined
 */

ltl invariant { [] ((P@CS) -> (mutex == 1)) }
