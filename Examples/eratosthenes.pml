/*
	The Sieve of Eratosthenes (c. 276-196 BC)
	Prints all prime numbers up to MAX
*/
#define MAX	25

mtype = { number, eof };

chan root = [0] of { mtype, int };

proctype sieve(chan c; int prime)
{	chan child = [0] of { mtype, int };
	bool haschild;
	int n;

	printf("MSC: %d is prime\n", prime);
end:	do
	:: c?number(n) ->
		if
		:: (n%prime) == 0 ->
			printf("MSC: %d = %d*%d\n", n, prime, n/prime)
		:: else ->
			if
			:: !haschild ->	/* new prime */
				haschild = true;
				run sieve(child, n);
			:: else ->
				child!number(n)
			fi;
		fi
	:: c?eof(0) ->
		break
	od;
	if
	:: haschild ->
		child!eof(0)
	:: else
	fi
}

init
{	int n = 2;

	run sieve(root, n);
	do
	:: (n <  MAX) -> n++; root!number(n)
	:: (n >= MAX) -> root!eof(0); break
	od
}
