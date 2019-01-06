#if 0
	Cambridge Ring Protocol [Needham 82]
	basic protocol - no LTL properties

	LOSS	RELAXED     states	 depth
	0	0	   482,061	 9,232	no reduction
	1	0	   993,547	10,234	no reduction
	0	1	   629,079	18,268	no reduction
	1	1	 1,252,660	17,117	no reduction
#endif

#define LOSS	1
#define RELAXED	1

#if RELAXED==1
#define stimeout	empty(sender)
#define rtimeout	empty(recv)
#else
#define stimeout	timeout
#define rtimeout	timeout
#endif

#define QSZ	6	/* length of message queues - should be 6 */

	mtype =	{
		RDY, NOTRDY, DATA, NODATA, RESET
	};
	chan sender	= [QSZ] of { mtype, byte };
	chan recv	= [QSZ] of { mtype, byte };

active proctype Sender()
{	short n = -1; byte t,m;

	xr sender;
	xs recv;

I:		/* Idle State */
		do
#if LOSS==1
		:: sender?_,_ -> progress2: skip
#endif
		:: sender?RESET,0 ->
ackreset:		recv!RESET,0;	/* stay in idle */
			n = -1;
			goto I

		/* E-rep: protocol error */

		:: sender?RDY,m ->		/* E-exp */
			assert(m == (n+1)%4);
advance:		n = (n+1)%4;
			if
/* buffer */		:: atomic {
				printf("MSC: NEW\n");
				recv!DATA,n;
				goto E
			   }
/* no buffer */		:: recv!NODATA,n;
				goto N
			fi

		:: sender?NOTRDY,m ->	/* N-exp */
expected:		assert(m == (n+1)%4);
			goto I

		/* Timeout */
		/* ignored (p.154, in [Needham'82]) */

		:: goto reset

		od;

E:		/* Essential element sent, ack expected */
		do
#if LOSS==1
		:: sender?_,_ -> progress0: skip
#endif
		:: sender?RESET,0 ->
			goto ackreset

		:: sender?RDY,m ->
			if
			:: (m == n) ->		/* E-rep */
				goto retrans
			:: (m == (n+1)%4) ->	/* E-exp */
				goto advance
			fi

		:: sender?NOTRDY,m ->	/* N-exp */
			goto expected

		/* Timeout */
		:: stimeout ->
			printf("MSC: STO\n");
retrans:		recv!DATA,n	/* retransmit */

		:: goto reset

		od;


N:		/* Non-essential element sent */
		do
#if LOSS==1
		:: sender?_,_ -> progress1: skip
#endif
		:: sender?RESET,0 ->
			goto ackreset

		:: sender?RDY,m ->		/* E-rep */
			assert(m == n)		/* E-exp: protocol error */
			-> recv!NODATA,n	/* retransmit and stay in N */

		:: recv!DATA,n;		/* buffer ready event */
			goto E

		:: goto reset

		/* Timeout */
		/* ignored (p.154, in [Needham'82]) */
		od;

reset:		recv!RESET,0;
		do
#if LOSS==1
		:: sender?_,_ -> progress3: skip
#endif
		:: sender?t,m ->
			if
			:: t == RESET -> n = -1; goto I
			:: else	/* ignored, p. 152 */
			fi
		:: timeout ->	/* a real timeout */
			goto reset
		od
}

active proctype Receiver()
{	byte t, n, m, Nexp;

	xr recv;
	xs sender;

I:		/* Idle State */
		do
#if LOSS==1
		:: recv?_,_ -> progress2: skip
#endif
		:: recv?RESET,0 ->
ackreset:		sender!RESET,0;		/* stay in idle */
			n = 0; Nexp = 0;
			goto I

		:: atomic { recv?DATA(m) ->	/* E-exp */
			assert(m == n);
advance:		printf("MSC: EXP\n");
			n = (n+1)%4;
			assert(m == Nexp);
			Nexp = (m+1)%4;
			if
			:: sender!RDY,n; goto E
			:: sender!NOTRDY,n; goto N
			fi
		   }

		:: recv?NODATA(m) ->		/* N-exp */
			assert(m == n)

		/* Timeout: ignored */

	/* only receiver can initiate transfer; p. 156 */
	:: empty(recv) -> sender!RDY,n; goto E

		:: goto reset
		od;

E:
		do
#if LOSS==1
		:: recv?_,_ -> progress1: skip
#endif
		:: recv?RESET,0 ->
			goto ackreset

		:: atomic { recv?DATA(m) ->
			if
			:: ((m+1)%4 == n) ->		/* E-rep */
				printf("MSC: REP\n");
				goto retrans
			:: (m == n) ->			/* E-exp */
				goto advance
			fi
		   }

		:: recv?NODATA(m) ->		/* N-exp  */
			assert(m == n);
			goto I

		:: rtimeout ->
			printf("MSC: RTO\n");
retrans:		sender!RDY,n;
			goto E

		:: goto reset

		od;

N:
		do
#if LOSS==1
		:: recv?_,_ -> progress0: skip
#endif
		:: recv?RESET,0 ->
			goto ackreset

		:: recv?DATA(m) ->		/* E-rep */
			assert((m+1)%4 == n);	/* E-exp and N-exp: protocol error */
			printf("MSC: REP\n");
			sender!NOTRDY,n	/* retransmit and stay in N */

		:: sender!RDY,n ->		/* buffer ready event */
			goto E

		/* Timeout: ignored */

		:: goto reset

		od;

progress:
reset:		sender!RESET,0;
		do
#if LOSS==1
		:: recv?_,_ -> progress3: skip
#endif
		:: recv?t,m ->
			if
			:: t == RESET -> n = 0; Nexp = 0; goto I
			:: else	/* ignored, p. 152 */
			fi
		:: timeout ->	/* a real timeout */
			goto reset
		od
}
