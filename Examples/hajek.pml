/*
 * Hajek's THE protocol
 */

#define MAX	8
#define printf(a,b)	skip

chan q0 = [1] of { bit, byte };
chan q1 = [1] of { bit, byte };

proctype station(chan inp, out)
{	bit phased, phase, everaccepted, everfetched, c, v;
	bit gotack = 1;
	byte din, prev_din, dout=1;

	do
	:: empty(inp) ->
		printf("%d empty\n", _pid);
		c = 1;
		goto pr
	:: inp?v,din ->
		if
		:: c = 0
		:: c = 1
		fi;
pr:		if
		:: c == 0 ->
			if
			:: (!everaccepted && v) || (v != phased) ->
				gotack = 1;
			:: else
			fi;
			if
			:: (v != phased) || (!everaccepted) ->
				printf("%d accept\n", _pid);
				assert(din == (prev_din+1)%MAX); /* ACCEPT */
				prev_din = din;
				everaccepted = 1;
				phased = v;
				phase = 1 - phase
			:: else
			fi
				
		:: c != 0 ->
			printf("%d error\n", _pid);
		fi;
		if
		:: gotack ->
			if
			:: everfetched ->
progress:			printf("%d fetch\n", _pid);
				dout = (dout+1)%MAX
			:: else
			fi;
			everfetched = 1
		:: else
		fi;
		out!phase,dout;
		gotack = 0
	od
}

init {
	atomic {
		run station(q0, q1);
		run station(q1, q0)
	}
}
