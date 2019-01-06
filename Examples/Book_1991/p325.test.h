proctype test_sender(bit n)
{	byte type, toggle;

	ses_to_flow[n]!sync,toggle;
	do
	:: flow_to_ses[n]?sync_ack,type ->
		if
		:: (type != toggle)
		:: (type == toggle) -> break
		fi
	:: timeout ->
		ses_to_flow[n]!sync,toggle
	od;
	toggle = 1 - toggle;

	do
	:: ses_to_flow[n]!data,white
	:: ses_to_flow[n]!data,red -> break
	od;
	do
	:: ses_to_flow[n]!data,white
	:: ses_to_flow[n]!data,blue -> break
	od;
	do
	:: ses_to_flow[n]!data,white
	:: break
	od
}
proctype test_receiver(bit n)
{
	do
	:: flow_to_ses[n]?data,white
	:: flow_to_ses[n]?data,red -> break
	od;
	do
	:: flow_to_ses[n]?data,white
	:: flow_to_ses[n]?data,blue -> break
	od;
end:	do
	:: flow_to_ses[n]?data,white
	od
}
