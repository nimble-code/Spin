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
init {	run split() }
