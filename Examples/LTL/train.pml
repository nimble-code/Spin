/*
 * modified uppaal train/gate example
 * removed assumptions about relative speeds
 */

/* see end of file for LTL properties */

#define N	4

mtype = { appr, leave, go, stop, Empty, Notempty, add, rem, hd };

chan g    = [N] of { mtype, pid };
chan qg   = [0] of { mtype, pid };
chan q    = [0] of { mtype, pid };
chan t[N] = [0] of { mtype };

active [N] proctype train()
{
	assert(_pid >= 0 && _pid < N);
Safe:	do
	:: g!appr(_pid);
Approaching:	if
		:: t[_pid]?go ->
			goto Start
		:: t[_pid]?stop
		fi;
Stopped:	t[_pid]?go;
Start:		skip; /* crossing */
Crossed:	g!leave(_pid)
	od
}

active proctype gate()
{	pid who;
Free:
	if
	:: qg?Empty(_) ->
		g?appr(who);
Add1:		q!add(who)
	:: qg?Notempty(who)
	fi;
	t[who]!go;
Occupied:
	do
	:: g?appr(who)  ->
		t[who]!stop;
Add2:		q!add(who)
	:: g?leave(who) ->
		q!rem(who);
		goto Free
	od
}

chan list = [N] of { pid };

active proctype queue()
{	pid who, x;
Start:
	if
	:: nempty(list) ->
		list?<who>;
		qg!Notempty(who)
	:: empty(list) ->
		qg!Empty(0)
	fi;
	do
	:: q?add(who) ->
		list!who
	:: q?rem(who) ->
Shiftdown:	list?x;
		assert(x == who);
		goto Start
	od
}

/*
 * ltl format specifies positive properties
 * that should be satisfied -- spin will
 * look for counter-examples to these properties
 */

ltl c1	{ []<> (gate@Occupied) }
ltl c2	{ []<> (train[0]@Crossed) }
ltl c3	{ []<> (train[0]@Crossed && train[1]@Stopped) }
ltl c4	{ []<> (train[0]@Crossed && train[1]@Stopped && train[2]@Stopped && train[3]@Stopped) }
ltl c5	{ [] (train[0]@Crossed + train[1]@Crossed + train[2]@Crossed + train[3]@Crossed <= 1) }
ltl c6	{ [] (len(list) < N) }

ltl c7	{ [] (((gate@Add1 || gate@Add2)) -> (len(list) < N)) }
ltl c8	{ [] (train[0]@Approaching) -> <> (train[0]@Crossed) }
