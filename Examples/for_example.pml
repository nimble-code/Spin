typedef m {
	bool b;
	int i;
	chan c;
}

init {
	m foo;
	chan x = [8] of { m };
	int i;

	foo.b = true;
	foo.i = 12;
	foo.c = x;
	x!foo;

	foo.b = false;
	foo.i = 10;
	foo.c = 0;
	x!foo; x!foo;

	i = 1;
	for (foo in x) {
		printf("%d: %d %d %d (len(x)=%d)\n",
			i, foo.b, foo.i, foo.c, len(x));
		i++
	}
}
