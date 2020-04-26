proctype A(chan q1)
{	chan q2;

	q1?q2;
	q2!123
}

proctype B(chan qforb)
{	int x;

	qforb?x;
	printf("x = %d\n", x)
}

init
{	chan qname[2] = [1] of { chan };
	chan qforb = [1] of { int };

	run A(qname[0]);
	run B(qforb);

	qname[0]!qforb
}
