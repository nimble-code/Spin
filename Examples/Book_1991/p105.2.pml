proctype fact(int n; chan p)
{	int result;
	chan child = [1] of { int };

	if
	:: (n <= 1) -> p!1
	:: (n >= 2) ->
		run fact(n-1, child);
		child?result;
		p!n*result
	fi
}
init
{	int result;
	chan child = [1] of { int };

	run fact(7, child);
	child?result;
	printf("result: %d\n", result)
}
