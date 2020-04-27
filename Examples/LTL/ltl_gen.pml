/* Generate all LTL formula with 4 or fewer operators */
/* Ed Gamble and Gerard Holzmann, November 2010 */
/* to run:
   spin -a ltl_gen.pml
   cc -DPRINTF -o pan pan.c
   ./pan
*/

#define DEPTH_LIMIT	4
#define NUMBER_OF_NODES	31 /* worst case: 1 + 2 + 4 + 8 binops + 16 leaves   */

#define Operator mtype
mtype = { NoOp, UnOp, BiOp };

#define Action mtype
mtype = { Always, Eventually, Next, Not, Until, And, Or, Implies, Equiv };

#define NodeId    byte
typedef Node {
    Operator op;
    NodeId    f;
    NodeId    g;
    Action    act;
};

Node nodes[NUMBER_OF_NODES];

#define Descend(X) \
		printf(" ("); \
			n = _nr_pr; \
			run view (nodes[this].X, next); \
			(n == _nr_pr) -> \
		printf(") ")

#define Unary(s)	printf(#s); Descend(f)

#define Binary(s)	Descend(f); printf(#s); Descend(g)

proctype view ( byte this, next )
{   byte n;
    if
    :: this <= next -> 
	if
	:: nodes[this].op == UnOp ->
		if
		:: nodes[this].act == Always     -> Unary([])
		:: nodes[this].act == Eventually -> Unary(<>)
		:: nodes[this].act == Next       -> Unary(X)
		:: nodes[this].act == Not        -> Unary(!)
		fi

	:: nodes[this].op == BiOp ->
		if
		:: nodes[this].act == Until   -> Binary(U)
		:: nodes[this].act == And     -> Binary(&&)
		:: nodes[this].act == Or      -> Binary(||)
		:: nodes[this].act == Implies -> Binary(->)
		:: nodes[this].act == Equiv   -> Binary(<->)
		fi

	:: nodes[this].op == NoOp ->
		printf ("p%d ", this)

	:: else -> assert(false)
	fi;
        this++
    :: else
    fi
}

init {
    byte depth = 0;
    NodeId next = 0;
    NodeId this = 0;
    NodeId dpth = 0;

    do
    :: depth < DEPTH_LIMIT -> 
        if
        :: nodes[this].op = NoOp
        :: nodes[this].op = UnOp;
		next++;
		nodes[this].f = next;
	        if
		:: nodes[this].act = Always
		:: nodes[this].act = Eventually
		:: nodes[this].act = Next
		:: nodes[this].act = Not
		fi
        :: nodes[this].op = BiOp;
		next++;	nodes[this].f = next;
		next++; nodes[this].g = next;
	        if
		:: nodes[this].act = Until
		:: nodes[this].act = And
		:: nodes[this].act = Or
		:: nodes[this].act = Implies
		:: nodes[this].act = Equiv
		fi
        fi;

        if
        :: this == next -> break
        :: else
        fi;

        if
        :: dpth == this -> dpth = next; depth++
        :: else
        fi;

        this++;

    :: else -> /* Depth reached; Fill leaves with NoOp */
        do   
        :: this <= next ->	nodes[this].op = NoOp;	this++
        :: else -> break
        od;
        break
    od;
    assert (this != NUMBER_OF_NODES);
#if 1
	printf("ltl { ");
	run view(0, next);
	_nr_pr == 1;
	printf(" }\n")
#endif
}
