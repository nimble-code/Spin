proctype upper()
{	byte s_state, r_state;
	byte type, toggle;

	ses_to_flow[0]!sync,toggle;
	do
	:: flow_to_ses[0]?sync_ack,type ->
		if
		:: (type != toggle)
		:: (type == toggle) -> break
		fi
	:: timeout ->
		ses_to_flow[0]!sync,toggle
	od;
	toggle = 1 - toggle;

	do
	/* sender */
	:: ses_to_flow[0]!white,0
	:: atomic {
		(s_state == 0 && len (ses_to_flow[0]) < QSZ) ->
		ses_to_flow[0]!red,0 ->
		s_state = 1
	   }
	:: atomic {
		(s_state == 1 && len (ses_to_flow[0]) < QSZ) ->
		ses_to_flow[0]!blue,0 ->
		s_state = 2
	   }
	/* receiver */
	:: flow_to_ses[1]?white,0
	:: atomic {
		(r_state == 0 && flow_to_ses[1]?[red]) ->
		flow_to_ses[1]?red,0 ->
		r_state = 1
	   }
	:: atomic {
		(r_state == 0 && flow_to_ses[1]?[blue]) ->
		assert(0)
	   }
	:: atomic {
		(r_state == 1 && flow_to_ses[1]?[blue]) ->
		flow_to_ses[1]?blue,0;
		break
	   }
	:: atomic {
		(r_state == 1 && flow_to_ses[1]?[red]) ->
		assert(0)
	   }
	od;
end:
	do
	:: flow_to_ses[1]?white,0
	:: flow_to_ses[1]?red,0 -> assert(0)
	:: flow_to_ses[1]?blue,0 -> assert(0)
	od
}
