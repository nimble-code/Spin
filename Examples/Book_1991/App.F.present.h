/*
 * Presentation Layer Validation Model
 */

proctype present(bit n)
{	byte status, uabort;

endIDLE:
	do
	:: use_to_pres[n]?transfer ->
		uabort = 0;
		break
	:: use_to_pres[n]?abort ->
		skip
	od;

TRANSFER:
	pres_to_ses[n]!transfer;
	do
	:: use_to_pres[n]?abort ->
		if
		:: (!uabort) ->
			uabort = 1;
			pres_to_ses[n]!abort
		:: (uabort) ->
			assert(1+1!=2)
		fi
	:: ses_to_pres[n]?accept,0 ->
		goto DONE
	:: ses_to_pres[n]?reject(status) ->
		if
		:: (status == FATAL || uabort) ->
			goto FAIL
		:: (status == NON_FATAL && !uabort) ->
progress:		goto TRANSFER
		fi
	od;
DONE:
	pres_to_use[n]!accept;
	goto endIDLE;
FAIL:
	pres_to_use[n]!reject;
	goto endIDLE
}
