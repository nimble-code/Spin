/* Snooping cache algorithm
 * used in a study at Bell Labs in the early eighties, and
 * said to be based on Goodman's work. Compare for instance:
 * "Using cache memory to reduce processor memory traffic",
 * by J.R. Goodman,  Proc. 10th Int. Symp. on Computer Architecture,
 * June 1983, pp. 124-131.
 */

#define QSZ	2

mtype = {	r, w, raw,
		RD, WR, RX,
		MX, MXdone,
		req0, req1,
		CtoB, BtoC,
		grant, done
	};

chan tocpu0	= [QSZ] of { mtype };
chan fromcpu0	= [QSZ] of { mtype };
chan tobus0	= [QSZ] of { mtype };
chan frombus0	= [QSZ] of { mtype };
chan grant0	= [QSZ] of { mtype };

chan tocpu1	= [QSZ] of { mtype };
chan fromcpu1	= [QSZ] of { mtype };
chan tobus1	= [QSZ] of { mtype };
chan frombus1	= [QSZ] of { mtype };
chan grant1	= [QSZ] of { mtype };

chan claim0	= [QSZ] of { mtype };
chan claim1	= [QSZ] of { mtype };
chan release0	= [QSZ] of { mtype };
chan release1	= [QSZ] of { mtype };

#define W	1
#define R	2
#define X	3

proctype cpu0()
{
	xs fromcpu0;
	xr tocpu0;
	do
	:: fromcpu0!r   -> tocpu0?done
	:: fromcpu0!w   -> tocpu0?done
	:: fromcpu0!raw -> tocpu0?done
	od
}

proctype cpu1()
{
	xs fromcpu1;
	xr tocpu1;
	do
	:: fromcpu1!r   -> tocpu1?done
	:: fromcpu1!w   -> tocpu1?done
	:: fromcpu1!raw -> tocpu1?done
	od
}

proctype cache0()
{	byte state = X;
	byte which;

	xr frombus0;
	xr fromcpu0;
	xs tocpu0;
	xs tobus0;
	xr grant0;
	xs claim0;
	xs release0;
resume:
	do
	:: frombus0?RD ->
		if
		:: (state == W) -> state = R; tobus0!CtoB
		:: (state != W) -> tobus0!done
		fi
	:: frombus0?MX -> state = X; tobus0!MXdone
	:: frombus0?RX ->
		if
		:: (state == W) -> state = X; tobus0!CtoB
		:: (state == R) -> state = X; tobus0!done
		:: (state == X) -> tobus0!done
		fi

	:: fromcpu0?r ->
		if
		:: (state != X) -> tocpu0!done
		:: (state == X) -> which = RD; goto buscycle
		fi
	:: fromcpu0?w ->
		if
		:: (state == W) -> tocpu0!done
		:: (state != W) -> which = MX; goto buscycle
		fi
	:: fromcpu0?raw ->
		if
		:: (state == W) -> tocpu0!done
		:: (state != W) -> which = RX; goto buscycle
		fi
	od;
buscycle:
	claim0!req0;
	do
	:: frombus0?RD ->
		if
		:: (state == W) -> state = R; tobus0!CtoB
		:: (state != W) -> tobus0!done
		fi
	:: frombus0?MX -> state = X; tobus0!MXdone
	:: frombus0?RX ->
		if
		:: (state == W) -> state = X; tobus0!CtoB
		:: (state == R) -> state = X; tobus0!done
		:: (state == X) -> tobus0!done
		fi
	:: grant0?grant ->
		if
		:: (which == RD) -> state = R
		:: (which == MX) -> state = W
		:: (which == RX) -> state = W
		fi;
		tocpu0!done;
		break
	od;
	release0!done;

	if
	:: (which == RD) -> tobus0!RD -> frombus0?BtoC
	:: (which == MX) -> tobus0!MX -> frombus0?done
	:: (which == RX) -> tobus0!RX -> frombus0?BtoC
	fi;
	goto resume
}

proctype cache1()
{	byte state = X;
	byte which;

	xr frombus1;
	xr fromcpu1;
	xs tobus1;
	xs tocpu1;
	xr grant1;
	xs claim1;
	xs release1;
resume:
	do
	:: frombus1?RD ->
		if
		:: (state == W) -> state = R; tobus1!CtoB
		:: (state != W) -> tobus1!done
		fi
	:: frombus1?MX -> state = X; tobus1!MXdone
	:: frombus1?RX ->
		if
		:: (state == W) -> state = X; tobus1!CtoB
		:: (state == R) -> state = X; tobus1!done
		:: (state == X) -> tobus1!done
		fi

	:: fromcpu1?r ->
		if
		:: (state != X) -> tocpu1!done
		:: (state == X) -> which = RD; goto buscycle
		fi
	:: fromcpu1?w ->
		if
		:: (state == W) -> tocpu1!done
		:: (state != W) -> which = MX; goto buscycle
		fi
	:: fromcpu1?raw ->
		if
		:: (state == W) -> tocpu1!done
		:: (state != W) -> which = RX; goto buscycle
		fi
	od;
buscycle:
	claim1!req1;
	do
	:: frombus1?RD ->
		if
		:: (state == W) -> state = R; tobus1!CtoB
		:: (state != W) -> tobus1!done
		fi
	:: frombus1?MX -> state = X; tobus1!MXdone
	:: frombus1?RX ->
		if
		:: (state == W) -> state = X; tobus1!CtoB
		:: (state == R) -> state = X; tobus1!done
		:: (state == X) -> tobus1!done
		fi
	:: grant1?grant ->
		if
		:: (which == RD) -> state = R
		:: (which == MX) -> state = W
		:: (which == RX) -> state = W
		fi;
		tocpu1!done;
		break
	od;
	release1!done;

	if
	:: (which == RD) -> tobus1!RD -> frombus1?BtoC
	:: (which == MX) -> tobus1!MX -> frombus1?done
	:: (which == RX) -> tobus1!RX -> frombus1?BtoC
	fi;
	goto resume
}

proctype busarbiter()
{
	xs grant0;
	xs grant1;
	xr claim0;
	xr claim1;
	xr release0;
	xr release1;

	do
	:: claim0?req0 -> grant0!grant; release0?done
	:: claim1?req1 -> grant1!grant; release1?done
	od
}

proctype bus()		/* models real bus + main memory */
{
	xs frombus1;
	xs frombus0;
	xr tobus0;
	xr tobus1;

	do
	:: tobus0?CtoB -> frombus1!BtoC
	:: tobus1?CtoB -> frombus0!BtoC

	:: tobus0?done -> /* M -> B */ frombus1!BtoC
	:: tobus1?done -> /* M -> B */ frombus0!BtoC

	:: tobus0?MXdone -> /* B -> M */ frombus1!done
	:: tobus1?MXdone -> /* B -> M */ frombus0!done

	:: tobus0?RD -> frombus1!RD
	:: tobus1?RD -> frombus0!RD

	:: tobus0?MX -> frombus1!MX
	:: tobus1?MX -> frombus0!MX

	:: tobus0?RX -> frombus1!RX
	:: tobus1?RX -> frombus0!RX
	od
}

init {
	atomic {
		run cpu0(); run cpu1();
		run cache0(); run cache1();
		run bus(); run busarbiter()
	}
}
