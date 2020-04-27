#define N    128
#define size  16

chan inp   = [size] of { short };
chan large = [size] of { short };
chan small = [size] of { short };

proctype split()
{	short cargo;

	do
	:: inp?cargo ->
		if
		:: (cargo >= N) -> large!cargo
		:: (cargo <  N) -> small!cargo
		fi
	od
}
proctype merge()
{	short cargo;

	do
	::	if
		:: large?cargo
		:: small?cargo
		fi;
		inp!cargo
	od
}
init
{	inp!345; inp!12; inp!6777; inp!32; inp!0;
	run split(); run merge()
}

