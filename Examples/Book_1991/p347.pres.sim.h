/*
 * PROMELA Validation Model
 * Presentation & User Layer - combined and reduced
 */

proctype present(bit n)
{	byte status;
progress0:
	pres_to_ses[n]!transfer ->
	do
	:: pres_to_ses[n]!abort;
progress1:	skip
	:: ses_to_pres[n]?accept,status ->
			break
	:: ses_to_pres[n]?reject,status ->
		if
		:: (status == NON_FATAL) ->
			goto progress0
		:: (status != NON_FATAL) ->
			break
		fi
	od
}
