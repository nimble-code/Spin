/*
	Example of property-based slicing.
	Try:	spin -A wordcount
	Requires Spin version 3.4 or later
 */

chan STDIN;
int c, nl, nw, nc;

init {
        bool inword = false;

        do
        :: STDIN?c ->
                if
                :: c == -1 ->   break	/* EOF */
                :: c == '\n' -> nc++; nl++
                :: else ->      nc++
                fi;
                if
                :: c == ' ' || c == '\t' || c == '\n' ->
                        inword = false
                :: else ->
                        if
                        :: !inword ->
                                nw++; inword = true
                        :: else /* do nothing */
                        fi
                fi
        od;
	assert(nc >= nl);
        printf("%d\t%d\t%d\n", nl, nw, nc)
}
