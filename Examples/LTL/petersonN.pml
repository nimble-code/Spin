/* Peterson's algorithm for N processes - see Lynch's book, p. 284 */

#define N	5	/* nr of processes */

byte turn[N], flag[N];

byte ncrit;	/* auxiliary var to check mutual exclusion */

active [N] proctype user()
{	byte j, k;
	/* the _pid's are: 0 .. N-1 */
again:
	k = 0;	/* count max N-1 rounds of competition */
	do
	:: k < N-1 ->
		flag[_pid] = k;
		turn[k] = _pid;

		j = 0;		/* for all j != _pid */
		do
		:: j == _pid ->
			j++
		:: j != _pid ->
			if
			:: j < N ->
				(flag[j] < k || turn[k] != _pid);
				j++
			:: j >= N  ->
				break
			fi
		od;
		k++
	:: else ->	/* survived all N-1 rounds */
		break
	od;

	ncrit++;
cs:	assert(ncrit == 1);	/* critical section */
	ncrit--;

	flag[_pid] = 0;
	goto again
}

ltl bounded_bypass { user[1]@again -> <> user[1]@cs }
