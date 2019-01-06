/*
 * PROMELA Validation Model
 * Session Layer
 */

#include "p337.defines2.h"
#include "p337.user.h"
#include "App.F.present.h"
#include "p337.session.h"
#include "p337.fserver.h"

init
{	atomic {
	  run userprc(0); run userprc(1);
	  run present(0); run present(1);
	  run session(0); run session(1);
	  run fserver(0); run fserver(1);
	  flow_to_ses[0] = ses_to_flow[1];
	  flow_to_ses[1] = ses_to_flow[0]
	}
}
