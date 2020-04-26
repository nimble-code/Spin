/* Dolev, Klawe & Rodeh for leader election in unidirectional ring
 * `An O(n log n) unidirectional distributed algorithm for extrema
 * finding in a circle,'  J. of Algs, Vol 3. (1982), pp. 245-260

 * Randomized initialization added -- Feb 17, 1997
 */

/* sample properties:
 *	<>  elected
 *	<>[]oneLeader
 *	[] (noLeader U oneLeader)
 *	![] noLeader
 *
 * ltl format specifies positive properties
 * that should be satisfied -- spin will
 * look for counter-examples to these properties
 */

byte nr_leaders = 0;

/* enclose ltl formula in $..$ if preprocessing symbols are used
  (they are not used below, but this illustrates the basic idea)
  use either <> or the word 'eventually'
  other word-equivalents: 'always' 'until' and 'not'
  enclose state expressions in (parentheses)
  the following two sets of formula are equivalent:

	ltl p0 $ eventually ( nr_leaders > 0 ) $
	ltl p1 $ eventually always ( nr_leaders == 1 ) $
	ltl p2 $ always ( (nr_leaders == 0) U (nr_leaders == 1) ) $
	ltl p3 $ not always ( nr_leaders == 0 ) $
*/
	ltl p0	{<> (nr_leaders > 0)}
	ltl p1	{<>[] (nr_leaders == 1)}
	ltl p2	{[] ((nr_leaders == 0) U (nr_leaders == 1))}
	ltl p3	{![] (nr_leaders == 0)}

#define N	5	/* number of processes in the ring */
#define L	10	/* 2xN */
byte I;

mtype = { one, two, winner };
chan q[N] = [L] of { mtype, byte};

proctype nnode (chan inp, out; byte mynumber)
{	bit Active = 1, know_winner = 0;
	byte nr, maximum = mynumber, neighbourR;

	xr inp;
	xs out;

	printf("MSC: #%d\n", mynumber);
	out!one(mynumber);
end:	do
	:: inp?one(nr) ->
		if
		:: Active -> 
			if
			:: nr != maximum ->
				out!two(nr);
				neighbourR = nr
			:: else ->
				know_winner = 1;
				out!winner,nr;
			fi
		:: else ->
			out!one(nr)
		fi

	:: inp?two(nr) ->
		if
		:: Active -> 
			if
			:: neighbourR > nr && neighbourR > maximum ->
				maximum = neighbourR;
				out!one(neighbourR)
			:: else ->
				Active = 0
			fi
		:: else ->
			out!two(nr)
		fi
	:: inp?winner,nr ->
		if
		:: nr != mynumber ->
			printf("MSC: LOST\n");
		:: else ->
			printf("MSC: LEADER\n");
			nr_leaders++;
			assert(nr_leaders == 1)
		fi;
		if
		:: know_winner
		:: else -> out!winner,nr
		fi;
		break
	od
}

init {
	byte proc;
	byte Ini[6];	/* N<=6 randomize the process numbers */
	atomic {

		I = 1;	/* pick a number to be assigned 1..N */
		do
		:: I <= N ->
			if	/* non-deterministic choice */
			:: Ini[0] == 0 && N >= 1 -> Ini[0] = I
			:: Ini[1] == 0 && N >= 2 -> Ini[1] = I
			:: Ini[2] == 0 && N >= 3 -> Ini[2] = I
			:: Ini[3] == 0 && N >= 4 -> Ini[3] = I
			:: Ini[4] == 0 && N >= 5 -> Ini[4] = I
			:: Ini[5] == 0 && N >= 6 -> Ini[5] = I	/* works for up to N=6 */
			fi;
			I++
		:: I > N ->	/* assigned all numbers 1..N */
			break
		od;

		proc = 1;
		do
		:: proc <= N ->
			run nnode (q[proc-1], q[proc%N], Ini[proc-1]);
			proc++
		:: proc > N ->
			break
		od
	}
}
