mtype { one, two, three }

mtype:fruit = { appel, pear, banana }

mtype:sizes = { small, medium, large }

chan q = [0] of { mtype, mtype:fruit, mtype:sizes, int }

proctype recipient(mtype:fruit z; mtype y)
{	mtype a
	mtype:fruit b
	mtype:sizes c

	atomic {
		printf("z: "); printm(z); printf("\n");
		printf("y: "); printm(y); printf("\n");
	}

	q?a,b,c,_
//	printf("%e %e %e\n", a, b, c)
	atomic {
		printm(a)
		printm(b)
		printm(c)
		printf("\n")
	}
	q?c,a,b,_			// type errors
//	printf("%e %e %e\n", a, b, c)
	atomic {
		printm(a)
		printm(b)
		printm(c)
		printf("\n")
	}
}

init {
	mtype numbers, nn;
	mtype:fruit snack, ss;
	mtype:sizes package, pp;

	run recipient(pear, two)
//	run recipient(small, two)	// type error

//	package = pear		// type error

	numbers = one
	snack = pear
	package = large

//	printf("%e %e %e\n", numbers, snack, package)	// only in simulation mode
	printm(numbers)
	printm(snack)
	printm(package)
	printf("\n")

	q!numbers,snack,large,9		// ok
//	q!large,ss,pp,3			// 1 type error

	assert(false)
}
