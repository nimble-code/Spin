/*
 * PROMELA Validation Model
 * global definitions
 */

#define QSZ		2	/* queue size     */

mtype = {
	red, white, blue,
	abort, accept, ack, sync_ack, close, connect,
	create, data, eof, open, reject, sync, transfer,
	FATAL, NON_FATAL, COMPLETE
	}

chan use_to_pres[2] = [QSZ] of { mtype };
chan pres_to_use[2] = [QSZ] of { mtype };
chan pres_to_ses[2] = [QSZ] of { mtype };
chan ses_to_pres[2] = [QSZ] of { mtype, byte };
chan ses_to_flow[2] = [QSZ] of { mtype, byte };
chan ses_to_fsrv[2] = [0] of { mtype };
chan fsrv_to_ses[2] = [0] of { mtype };
chan flow_to_ses[2];
