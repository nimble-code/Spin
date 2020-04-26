/*
 * PROMELA Validation Model
 * FLOW CONTROL LAYER VALIDATION
 */

/* see end of file for LTL properties */

#define LOSS		1	/* message loss   */
#define DUPS		0	/* duplicate msgs */
#define QSZ		2	/* queue size     */

mtype = {
	red, white, blue,
	abort, accept, ack, sync_ack, close, connect,
	create, data, eof, open, reject, sync, transfer,
	FATAL, NON_FATAL, COMPLETE
	}

chan ses_to_flow[2] = [QSZ] of { byte, byte };
chan flow_to_ses[2] = [QSZ] of { byte, byte };
chan dll_to_flow[2] = [QSZ] of { byte, byte };

/*
 * Flow Control Layer Validation Model
 */

#define true	1
#define false	0

#define M	4	/* range sequence numbers   */
#define W	2	/* window size: M/2         */

proctype fc(chan s2f, f2d, f2s, d2f)
{	bool	busy[M];	/* outstanding messages    */
	byte	q;		/* seq# oldest unacked msg */
	byte	m;		/* seq# last msg received  */
	byte	s;		/* seq# next msg to send   */
	byte	window;		/* nr of outstanding msgs  */
	byte	type;		/* msg type                */
	bit	received[M];	/* receiver housekeeping   */
	bit	x;		/* scratch variable        */
	byte	p;		/* seq# of last msg acked  */
	byte	I_buf[M], O_buf[M];	/* message buffers */

	xr s2f;
	xs f2d;
	xs f2s;
	xr d2f;

	/* sender part */
end:	do
	:: atomic {
	   (window < W	&& nempty(s2f)
			&& nfull(f2d)) ->
			s2f?type,x;
			window = window + 1;
			busy[s] = true;
			O_buf[s] = type;
			f2d!type,s;
			if
			:: (type != sync) ->
				s = (s+1)%M
			:: (type == sync) ->
				window = 0;
				s = M;
				do
				:: (s > 0) ->
					s = s-1;
					busy[s] = false
				:: (s == 0) ->
					break
				od
			fi
	   }
	:: atomic {
		(window > 0 && busy[q] == false) ->
		window = window - 1;
		q = (q+1)%M
	   }
#if DUPS
	:: atomic {
		(nfull(f2d) && window > 0 && busy[q] == true) ->
		f2d!O_buf[q],q
	   }
#endif
	:: atomic {
		(timeout && nfull(f2d) && window > 0 && busy[q] == true) ->
		f2d!O_buf[q],q
	   }
	/* receiver part */
#if LOSS
	:: d2f?type,m /* lose any message */
#endif
	:: d2f?type,m ->
		if
		:: atomic {
			(type == ack) ->
			busy[m] = false
		   }
		:: atomic {
			(type == sync) ->
			m = 0;
			do
			:: (m < M) ->
				received[m] = 0;
				m = m+1
			:: (m == M) ->
				break
			od
		   };	f2d!sync_ack,0
		:: (type == sync_ack) ->
			f2s!sync_ack,0
		:: (type != ack && type != sync && type != sync_ack)->
			if
			:: atomic {
				(received[m] == true) ->
					x = ((0<p-m   && p-m<=W)
					||   (0<p-m+M && p-m+M<=W)) };
					if
					:: (x) -> f2d!ack,m
					:: (!x)	/* else skip */
					fi
			:: atomic {
				(received[m] == false) ->
					I_buf[m] = type;
					received[m] = true;
					received[(m-W+M)%M] = false
			   }
			fi
		fi
	:: /* atomic { */
	   (received[p] == true && nfull(f2s) && nfull(f2d)) ->
		f2s!I_buf[p],0;
		f2d!ack,p;
		p = (p+1)%M
	   /* } */
	od
}

proctype upper_s(chan s2f, f2s0)
{	byte s_state;
	byte type, toggle;

	xs s2f;
	xr f2s0;

	s2f!sync,toggle;
	do
	:: f2s0?sync_ack,type ->
		if
		:: (type != toggle)
		:: (type == toggle) -> break
		fi
	:: timeout ->
		s2f!sync,toggle
	od;
	toggle = 1 - toggle;

end:	do
	:: s2f!white,0
	:: atomic {
		(s_state == 0 && nfull(s2f)) ->
		s2f!red,0 ->
		s_state = 1
	   }
	:: atomic {
		(s_state == 1 && nfull(s2f)) ->
		s2f!blue,0 ->
		s_state = 2
	   }
	od
}

proctype upper_r(chan f2s1)
{	byte r_state;

	xr f2s1;

	do
	:: f2s1?white,0
	:: f2s1?red,0 -> break
	:: f2s1?blue,0 -> assert(0)
	od;

	do
	:: f2s1?white,0
	:: f2s1?red,0 -> assert(0)
	:: f2s1?blue,0 -> goto end
	od;
end:
	do
	:: f2s1?white,0
	:: f2s1?red,0 -> assert(0)
	:: f2s1?blue,0 -> assert(0)
	od
}

init
{
	atomic {
	  run fc(ses_to_flow[0], dll_to_flow[1], flow_to_ses[0], dll_to_flow[0]);
	  run fc(ses_to_flow[1], dll_to_flow[0], flow_to_ses[1], dll_to_flow[1]);
	  run upper_s(ses_to_flow[0], flow_to_ses[0]);
	  run upper_r(flow_to_ses[1])
	}
}

ltl p1 { ( len(flow_to_ses[1]) > 0 -> flow_to_ses[1]?[white]) U ( flow_to_ses[1]?[red] ) }
ltl p2 { (!(flow_to_ses[1]?[blue])) U (flow_to_ses[1]?[red]) }
ltl p3 { <> (flow_to_ses[1]?[blue]) }
