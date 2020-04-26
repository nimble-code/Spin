#define p	0
#define v	1

chan sema = [0] of { bit };	/* typo in original `=' was missing */

proctype dijkstra()
{	do
	:: sema!p -> sema?v
	od	
}
byte count;

proctype user()
{	sema?p;
	count = count+1;
	skip;	/* critical section */
	count = count-1;
	sema!v;
	skip	/* non-critical section */
}
proctype monitor() { assert(count == 0 || count == 1) }
init
{	atomic {
		run dijkstra(); run monitor();
		run user(); run user(); run user()
	}
}
