/*
 * Flow Control Layer Validation Model
 */

#define true	1
#define false	0

#define M	4	/* range sequence numbers   */
#define W	2	/* window size: M/2         */

proctype fc(bit n)
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

	/* sender part */
end:	do
	:: atomic {
	   (window < W	&& len(ses_to_flow[n]) >  0 &&
			   len(flow_to_dll[n]) < QSZ) ->
			ses_to_flow[n]?type,x;
			window = window + 1;
			busy[s] = true;
			O_buf[s] = type;
			flow_to_dll[n]!type,s;
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
		(len(flow_to_dll[n]) < QSZ
		 && window > 0 && busy[q] == true) ->
		flow_to_dll[n]!	O_buf[q],q
	   }
#endif
	:: atomic {
		(timeout && len(flow_to_dll[n]) < QSZ &&
		 window > 0 && busy[q] == true) ->
		flow_to_dll[n]!	O_buf[q],q
	   }

	/* receiver part */
#if LOSS
	:: dll_to_flow[n]?type,m /* lose any message */
#endif
	:: dll_to_flow[n]?type,m ->
		if
		:: atomic {
			(type == ack) ->
			busy[m] = false
		   }
		:: atomic {
			(type == sync) ->
			flow_to_dll[n]!sync_ack,m;
			m = 0;
			do
			:: (m < M) ->
				received[m] = 0;
				m = m+1
			:: (m == M) ->
				break
			od
		   }
		:: (type == sync_ack) ->
			flow_to_ses[n]!sync_ack,m
		:: (type != ack && type != sync && type != sync_ack)->
			if
			:: atomic {
				(received[m] == true) ->
					x = ((0<p-m   && p-m<=W) ||
					     (0<p-m+M && p-m+M<=W)) };
					if
					:: (x) -> flow_to_dll[n]!ack,m
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
	:: (received[p] == true && len(flow_to_ses[n])<QSZ &&
				   len(flow_to_dll[n])<QSZ) ->
		flow_to_ses[n]!I_buf[p],0;
		flow_to_dll[n]!ack,p;
		p = (p+1)%M
	od
}
