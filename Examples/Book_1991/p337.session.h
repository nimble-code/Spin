/*
 * Session Layer Validation Model
 */

proctype session(bit n)
{	bit toggle;
	byte type, status;

endIDLE:
	do
	:: pres_to_ses[n]?type ->
		if
		:: (type == transfer) ->
			goto DATA_OUT
		:: (type != transfer)	/* ignore */
		fi
	:: flow_to_ses[n]?type,0 ->
		if
		:: (type == connect) ->
			goto DATA_IN
		:: (type != connect)	/* ignore */
		fi
	od;

DATA_IN:		/* 1. prepare local file fsrver */
	ses_to_fsrv[n]!create;
	do
	:: fsrv_to_ses[n]?reject ->
		ses_to_flow[n]!reject,0;
		goto endIDLE
	:: fsrv_to_ses[n]?accept ->
		ses_to_flow[n]!accept,0;
		break
	od;
			/* 2. Receive the data, upto eof */
	do
	:: flow_to_ses[n]?data,0 ->
		ses_to_fsrv[n]!data
	:: flow_to_ses[n]?eof,0 ->
		ses_to_fsrv[n]!eof;
		break
	:: pres_to_ses[n]?transfer ->
		ses_to_pres[n]!reject(NON_FATAL)
	:: flow_to_ses[n]?close,0 ->	/* remote user aborted */
		ses_to_fsrv[n]!close;
		break
	:: timeout ->		/* got disconnected */
		ses_to_fsrv[n]!close;
		goto endIDLE
	od;
			/* 3. Close the connection */
	ses_to_flow[n]!close,0;
	goto endIDLE;

DATA_OUT:		/* 1. prepare local file fsrver */
	ses_to_fsrv[n]!open;
	if
	:: fsrv_to_ses[n]?reject ->
		ses_to_pres[n]!reject(FATAL);
		goto endIDLE
	:: fsrv_to_ses[n]?accept ->
		skip
	fi;
			/* 2. initialize flow control *** disabled
	ses_to_flow[n]!sync,toggle;
	do
	:: atomic {
		flow_to_ses[n]?sync_ack,type ->
		if
		:: (type != toggle)
		:: (type == toggle) -> break
		fi
	   }
	:: timeout ->
		ses_to_fsrv[n]!close;
		ses_to_pres[n]!reject(FATAL);
		goto endIDLE
	od;
	toggle = 1 - toggle;
			/* 3. prepare remote file fsrver */
	ses_to_flow[n]!connect,0;
	if
	:: flow_to_ses[n]?reject,0 ->
		ses_to_fsrv[n]!close;
		ses_to_pres[n]!reject(FATAL);
		goto endIDLE
	:: flow_to_ses[n]?connect,0 ->
		ses_to_fsrv[n]!close;
		ses_to_pres[n]!reject(NON_FATAL);
		goto endIDLE
	:: flow_to_ses[n]?accept,0 ->
		skip
	:: timeout ->
		ses_to_fsrv[n]!close;
		ses_to_pres[n]!reject(FATAL);
		goto endIDLE
	fi;
			/* 4. Transmit the data, upto eof */
	do
	:: fsrv_to_ses[n]?data ->
		ses_to_flow[n]!data,0
	:: fsrv_to_ses[n]?eof ->
		ses_to_flow[n]!eof,0;
		status = COMPLETE;
		break
	:: pres_to_ses[n]?abort ->	/* local user aborted */
		ses_to_fsrv[n]!close;
		ses_to_flow[n]!close,0;
		status = FATAL;
		break
	od;
			/* 5. Close the connection */
	do
	:: pres_to_ses[n]?abort 	/* ignore */
	:: flow_to_ses[n]?close,0 ->
		if
		:: (status == COMPLETE) ->
			ses_to_pres[n]!accept,0
		:: (status != COMPLETE) ->
			ses_to_pres[n]!reject(status)
		fi;
		break
	:: timeout ->
		ses_to_pres[n]!reject(FATAL);
		break
	od;
	goto endIDLE
}
