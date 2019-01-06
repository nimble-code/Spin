
mtype = {
/*1*/	ack,
/*2*/	can,
/*3*/	crcck,		/* checksum error */
/*4*/	data8,
/*5*/	last8,
/*6*/	nak,
/*7*/	query8,
/*8*/	rvnak,
/*9*/	zak
	};

chan StoC = [2] of { short, short };
chan CtoR = [2] of { short, short };
chan RtoC = [2] of { short, short };
chan RtoS = [2] of { short, short };

init {
	atomic {
	run sender(RtoS, StoC);
	run channel(StoC, CtoR);
	run receiver(CtoR, RtoS)
	}
}

proctype channel(chan inp, out)
{	short a, b; byte cnt;
	xr inp;
	xs out;
end:	do
	:: inp?a,b ->
		if
		:: out!a,b
		:: (cnt == 0 && a != zak) -> cnt = cnt+1; out!crcck,b
/*		:: (cnt == 0) -> cnt = cnt+1; out!-3,a
		:: (cnt == 0) -> cnt = cnt+1; out!-1,a
		:: (cnt == 0) -> cnt = cnt+1; out!-2,a
		:: (cnt == 0) -> cnt = cnt+1; out!-4,a
*/
		fi
	od
}

proctype sender(chan inp, out)
{	bit rcvrrdy;
	short state, queryt, datat, lastt;
	short t, type;
	short seqno, toff, offset, cnt, retries, maxretries;

	xs out;
start:
	atomic {
		offset	= 0;
		retries	= 0;
		maxretries = 6;
		rcvrrdy	= 0;
		state	= 2;
		datat	= data8;
		queryt	= query8;
		lastt	= last8;
		goto s1
	};

s1:
	if /* if we received an interrupt for incoming data */
	:: (len(inp)  > 0) -> state = 2
	:: (len(inp) == 0)
	fi;
	goto s2;

s2:
	if
	:: (state == 0) -> goto s3
	:: (state == 1) -> goto s4
	:: (state == 2) -> goto s7
	:: (state >= 3) -> goto s1
	fi;

s3:
	out!queryt,offset;
	state = 2;
	goto s1;

s4:
	atomic {
		if
		:: (offset < 3) -> type = datat
		:: (offset > 2) -> type = lastt
		fi;
		if
		:: (retries  > 0) -> type = queryt
		:: (retries <= 0)
		fi
	};
	out!type,offset;	/* it can fail, but ignore that */
	goto s6;
		
s5:
	out!can,-1;
	goto F;

s6:
	atomic {
		offset = offset + 1;	/* assume cnt > 0 */
		if
/*		:: goto s5		/* channel disconnected */
		:: (type == queryt || type == lastt) ->
			state = 2
		:: !(type == queryt || type == lastt)
		fi;
		goto s1
	};

s7:
	atomic {
		inp?t,seqno;
		if
		:: (t == zak) -> goto s8
		:: (t == ack) -> goto s9
		:: (t == nak) -> goto s12
		:: (t == -2) -> goto F		/* remote canceled */
		:: (t == -3) -> goto s13	/* serial port overrun or timeout */
		:: (t == crcck) -> goto s13
		:: !(t == zak
		||   t == ack
		||   t == nak
		||   t == -2
		||   t == -3
		||   t == crcck) ->
			goto s5
		fi
	};

s8:
	offset = seqno;
	out!zak,offset;
	goto S;

s9:
	toff = seqno;
	goto s10;

s10:
	atomic {
		retries = 0;
		if
		:: (offset > toff) ->	/* worthless ack */
			goto s1
		:: (offset <= toff) ->
			offset = toff;
			goto s11
		fi
	};

s11:
	atomic {
		if
		:: (!rcvrrdy) ->
			rcvrrdy = 1;
			maxretries = 5;
			/* ack/nak received - start transmit */
			retries = 0
		:: (rcvrrdy) ->
			skip
		fi;
		state = 1;
		goto s1
	};

s12:
	atomic {
		toff = seqno;
		if
		:: (toff >= offset) ->
			goto s10
		:: (toff < offset)
		fi;
		retries = retries+1;
		if
		:: (retries >= maxretries) ->
			goto s5
		:: (retries <  maxretries)
		fi;
		offset = toff;
		goto s11
	};

s13:
	atomic {
		if
		:: (retries >= maxretries) ->
			goto s5
		:: (retries <  maxretries) ->
			if
			:: (rcvrrdy) -> state = 1
			:: (!rcvrrdy) -> state = 0
			fi;
			goto s1
		fi
	};

F:	/* failure */
	assert(0);
S:	/* success */
	skip;
end:	do :: inp?t,seqno od
}

proctype receiver(chan inp, out)
{	short state, lasttyp;
	short offset, retries, lastack;
	short readStat, cnt, seqno;
	short rtype, type;
	short respreq, typ;

	xr inp;
start:
	atomic {
		offset	= 0;
		state	= 0;
		lasttyp	= 0;
		retries	= 0;
		lastack	= 0;
		rtype	= nak;
		readStat = 0;
		goto s4
	};

s2:
	if
	:: (readStat == -1
	||  readStat == -2
	||  readStat == -4) -> goto F
	:: (readStat == -3) -> goto s3
	:: (readStat >= 0) -> goto s4
	fi;

s3:
	atomic {
		if
	/*	:: rtype == rvnak -> goto s4	/* too soon */
		:: skip
		fi;
		retries = retries+1
	};
	if
	:: (retries >= 7) ->
		out!can,-1;
		goto F
	:: (retries < 7) ->
		skip
	fi;
	atomic {
		if
		:: (retries == 0) ->	/* how can it be zero ever? */
			state = 3
		:: (retries != 0) ->
			state = 0	/* send nak state */
		fi;
		goto s4
	};

s4:
	if
	:: (state == 0) -> goto s5
	:: (state == 1) -> goto s6
	:: (state == 2) -> goto s12
	:: (state >= 3) -> goto S
	fi;

s5:
	out!rtype,offset;
	state = 1;
	goto s4;

s6:
	atomic {
		inp?type,seqno;
		rtype = nak;	/* was:	rtype = rvnak */
		typ = ack;
		if
		:: (	type == -1
		|| 	type == -2)	-> goto s7
		:: (	type == -3
		||	type == crcck)	-> goto s3
		:: (	type == -4)	-> goto s11
		:: (	type == last8)	-> goto s8
		:: (	type == query8)	-> goto s9
		:: (	type == data8)	-> goto s10
		:: !(	type == -1
		||	type == -2
		||	type == -3 
		||	type == crcck
		||	type == -4
		||	type == last8
		||	type == query8
		||	type == data8) -> goto s11
		fi
	};

s7:
	readStat = type;
	goto s2;

s8:
	atomic {
		typ = zak;
		state = 2;
		goto s9
	};

s9:
	atomic {
		rtype = nak;
		respreq = 1;
		goto s10
	};

s10:
	atomic {
		if
		:: (seqno  > offset) ->
			goto s3
		:: (seqno == offset) ->
			cnt = 1
		:: (seqno  < offset) ->
			cnt = 0
		fi;
		if
		:: (cnt < 0) ->
			readStat = cnt;
			goto s2
		:: (cnt >= 0) ->
			skip
		fi;
		offset = offset + cnt
	};
	if
	:: (respreq) ->
		out!typ,offset;
		lastack = offset;
		lasttyp = typ
	:: !(respreq) ->
		skip
	fi;
	atomic {
		if
		:: (typ == zak) ->
			retries = -2
		:: (typ != zak) ->
			retries = 2
		fi;
		goto s4
	};

s11:
	out!can,-1;
	goto F;

s12:
	atomic {
		inp?type,seqno;
		if
		:: (type == -1) -> goto s13
		:: (type == -3) -> goto s13
		:: (type == -2) -> goto s11
		:: (type == -4) -> goto s11
		:: (type == query8
		||	type == last8
		||	type == data8
		||	type == crcck) -> goto s14
		:: !(type == -1
		||	type == -3
		||	type == -2
		||	type == -4
		||	type == query8
		||	type == last8
		||	type == data8
		||	type == crcck) -> goto S
		fi
	};

s13:
	readStat = type;
	goto s2;

s14:
	out!lasttyp,lastack;
	retries = -2;
	goto s4;

F:	assert(0);
S:	skip;
end:	do :: inp?type,seqno od
}

