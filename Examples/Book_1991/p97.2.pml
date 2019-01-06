proctype nr(short id, a, b)
{	int res;

atomic	{	res = (a*a+b)/2*a;
		printf("result %d: %d\n", id, res)
	}
}
init { run nr(1,1,1); run nr(1,2,2); run nr(1,3,2) }
