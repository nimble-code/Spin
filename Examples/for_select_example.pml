/* some simple examples of for and select */

#define N 10

typedef m {
	bit b;
	int x;
	chan c;
};

init {
	int i, j;
	chan a[N] = [7] of { m };
	chan b[4];
	m foo, bar, goo;

	select ( i : 8..21 );
	printf("i=%d\n", i);
	assert(i != 21);

	foo.b = 1;
	foo.x = 3;
	foo.c = a[3];
	a[3]!foo;

	bar.b = 0;
	bar.x = 978;
	bar.c = a[6];
	a[3]!bar;
/*
 * make sure to leave a space after the ..
 * or else the preprocessor will not see the N
 */
	for (i : 1 .. N) {
		printf("i = %d\n", i)
	}
	for (i in a) {
		printf("a[%d]\t", i);
		for (j in b) {
			printf("b[%d], ", j);
		}
		printf("\n");
	}

	for (goo in a[3]) {
		printf("goo: %d %d %d -- %d\t",
			goo.b, goo.x, goo.c, len(a[3]));
		for (foo in a[3]) {
			printf("foo: %d %d %d -- %d\t",
				foo.b, foo.x, foo.c, len(a[3]));
		}
		printf("\n");
	}

	a[3]?goo;
	printf("%d %d %d -- %d\n", goo.b, goo.x, goo.c, len(a[3]))
}
