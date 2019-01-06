active proctype loop()
{	byte a, b;

	do
	:: a = (a+1)%3;
		if
		:: b = 2*a; skip
		:: b = 2*a; accept: skip
		fi;
progress:	b--
	od
}
