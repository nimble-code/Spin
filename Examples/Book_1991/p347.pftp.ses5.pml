/*
 * PROMELA Validation Model
 * Session Layer
 */

#include "p337.defines2.h"
#include "p347.pres.sim.h"
#include "p347.session.prog.h"
#include "p337.fserver.h"

init
{	atomic {
	  run present(0); run present(1);
	  run session(0); run session(1);
	  run fserver(0); run fserver(1);
	  flow_to_ses[0] = ses_to_flow[1];
	  flow_to_ses[1] = ses_to_flow[0]
	}
}
