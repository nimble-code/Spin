/*
 * File Server Validation Model
 */

proctype fserver(bit n)
{
end:	do
	:: ses_to_fsrv[n]?create ->	/* incoming */
		if
		:: fsrv_to_ses[n]!reject
		:: fsrv_to_ses[n]!accept ->
			do
			:: ses_to_fsrv[n]?data
			:: ses_to_fsrv[n]?eof -> break
			:: ses_to_fsrv[n]?close -> break
			od
		fi
	:: ses_to_fsrv[n]?open ->		/* outgoing */
		if
		:: fsrv_to_ses[n]!reject
		:: fsrv_to_ses[n]!accept ->
			do
			:: fsrv_to_ses[n]!data -> progress: skip
			:: ses_to_fsrv[n]?close -> break
			:: fsrv_to_ses[n]!eof -> break
			od
		fi
	od
}
