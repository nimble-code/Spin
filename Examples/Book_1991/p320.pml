#define true	1
#define false	0
#define Aturn	false
#define Bturn	true

bool x, y, t;
bool ain, bin;

proctype A()
{	x = true;
	t = Bturn;
	(y == false || t == Aturn);
	ain = true;
	assert(bin == false);	/* critical section */
	ain = false;
	x = false
}

proctype B()
{	y = true;
	t = Aturn;
	(x == false || t == Bturn);
	bin = true;
	assert(ain == false);	/* critical section */
	bin = false;
	y = false
}

init
{	run A(); run B()
}
