#define p	0
#define v	1

chan sema = [0] of { bit };

proctype dijkstra()
{	do
	:: sema!p -> sema?v
	od	
}
proctype user()
{	sema?p;
	/* critical section */
	sema!v
	/* non-critical section */
}
init
{	atomic {
		run dijkstra();
		run user(); run user(); run user()
	}
}
