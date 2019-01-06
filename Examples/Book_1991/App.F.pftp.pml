/*
 * PROMELA Validation Model - startup script
 */

#include "App.F.defines.h"
#include "App.F.user.h"
#include "App.F.present.h"
#include "App.F.session.h"
#include "App.F.fserver.h"
#include "App.F.flow_cl.h"
#include "App.F.datalink.h"

init
{	atomic {
	  run userprc(0); run userprc(1);
	  run present(0); run present(1);
	  run session(0); run session(1);
	  run fserver(0); run fserver(1);
	  run fc(0);      run fc(1);
	  run data_link()
	}
}
