/*
 * Datalink Layer Validation Model
 */

proctype data_link()
{	byte type, seq;

end:    do
	:: flow_to_dll[0]?type,seq ->
		if
		:: dll_to_flow[1]!type,seq
		:: skip	/* lose message */
		fi
	:: flow_to_dll[1]?type,seq ->
		if
		:: dll_to_flow[0]!type,seq
		:: skip	/* lose message */
		fi
	od
}
