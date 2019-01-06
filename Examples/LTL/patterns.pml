init { printf("hello ltl\n") }
int P, Q, R, S, T, Z;

	/* Absence -- P is false: */
	/* Globally */		ltl a1 { [](!P) }
	/* Before R */		ltl a2 { <>R -> (!P U R) }
	/* After Q */		ltl a3 { [](Q -> [](!P)) }
	/* Between Q and R */	ltl a4 { []((Q && !R && <> R) -> (!P U R)) }
	/* After Q until R */	ltl a5 { [](Q && !R -> (!P W R)) }

	/* Existence -- P becomes true: */
	/* Globally */		ltl e1 { <>(P) }
	/* Before R */		ltl e2 { !R W (P && !R) }
	/* After Q */		ltl e3 { [](!Q || <>(Q && <>P)) }
	/* Between Q and R */	ltl e4 { [](Q && !R -> (!R W (P && !R))) }
	/* After Q until R */	ltl e5 { [](Q && !R -> (!R U (P && !R))) }

#if 0
	/* Bounded Existence  -- P occurs at most twice: [tends to be complex] */
	/* the next two formula can take a while to convert into never claims */
	/* Globally */		ltl be1 { (!P W (P W (!P W (P W []!P)))) }
	/* Before R */		ltl be2 { <>R -> ((!P && !R U (R || ((P && !R) U (R || ((!P && !R U (R || ((P && !R) U (R || (!P U R))))))))))) }

	/* for the next three spin runs out of memory */
	/* After Q */		ltl be3 { <>Q -> (!Q U (Q && (!P W (P W (!P W (P W []!P)))))) }
	/* Between Q and R */	ltl be4 { []((Q && <>R-> ((!P && !R U (R || ((P && !R) U (R || ((!P && !R U (R || ((P && !R) U (R || (!P U R))))))))))))) }
	/* After Q until R */	ltl be5 { [](Q -> ((!P && !R U (R || ((P && !R) U (R || ((!P && !R U (R || ((P && !R) U (R || (!P W R || []P)))))))))))) }
#endif

	/* Universality -- P is true:  */
	/* Globally */		ltl u1 { [](P) }
	/* Before R */		ltl u2 { <>R -> (P U R) }
	/* After Q */		ltl u3 { [](Q -> [](P)) }
	/* Between Q and R */	ltl u4 { []((Q && !R && <> R-> (P U R))) }
	/* After Q until R */	ltl u5 { [](Q && !R -> (P W R)) }

	/* Precedence -- S precedes P: */
	/* Globally */		ltl p1 { !P W S }
	/* Before R */		ltl p2 { <>R -> (!P U (S || R)) }
	/* After Q */		ltl p3 { []!Q || <>(Q && (!P W S)) }
	/* Between Q and R */	ltl p4 { []((Q && !R && <>R) -> (!P U (S || R))) }
	/* After Q until R */	ltl p5 { [](Q && !R -> (!P W (S || R))) }

	/* Response -- S responds to P: */
	/* Globally */		ltl r1 { [](P -> <>S) }
	/* Before R */		ltl r2 { <>R -> (P -> (!R U (S && !R))) U R }
	/* After Q */		ltl r3 { [](Q -> [](P -> <>S)) }
	/* Between Q and R */	ltl r4 { []((Q && !R && <>R) -> (P -> (!R U (S && !R))) U R) }
	/* After Q until R */	ltl r5 { [](Q && !R -> ((P -> (!R U (S && !R))) W R)) }

	/* Precedence Chain -- S, T precedes P: */
	/* Globally */		ltl pc1 { <>P -> (!P U (S && !P && X(!P U T))) }
	/* Before R */		ltl pc2 { <>R -> (!P U (R || (S && !P && X(!P U T)))) }
	/* After Q */		ltl pc3 { ([]!Q || (!Q U (Q && <>P -> (!P U (S && !P && X(!P U T)))))) }
	/* Between Q and R */	ltl pc4 { []((Q && <>R-> (!P U (R || (S && !P && X(!P U T)))))) }
	/* After Q until R */	ltl pc5 { [](Q -> (<>P -> (!P U (R || (S && !P && X(!P U T)))))) }

	/* Precedence Chain -- P precedes (S, T): */
	/* Globally */		ltl pc6 { (<>(S && X<>T) -> ((!S) U P)) }
	/* Before R */		ltl pc7 { <>R -> ((!(S && (!R && X(!R U (T && !R)))) U (R || P))) }
	/* After Q */		ltl pc8 { ([]!Q || ((!Q) U (Q && ((<>(S && X<>T)) -> ((!S) U P))))) }
	/* Between Q and R */	ltl pc9 { []((Q && <>R) -> ((!(S && (!R) && X(!R U (T && !R)))) U (R || P))) }
	/* After Q until R */	ltl pc10 { [](Q -> (!(S && (!R& X(!R U (T && !R))) U (R || P) || [](!(S && X<>T))))) }

	/* Response Chain -- P responds to S,T: */
	/* Globally */		ltl rc1 { [] (S && X<> T -> X(<>(T && <> P))) }
	/* Before R */		ltl rc2 { <>R -> (S && X(!R U T-> X(!R U (T && <> P))) U R) }
	/* After Q */		ltl rc3 { [] (Q -> [] (S && X<> T -> X(!T U (T && <> P)))) }
	/* Between Q and R */	ltl rc4 { [] ((Q && <>R) -> (S && X(!R U T) -> X(!R U (T && <> P))U R)) }
	/* After Q until R */	ltl rc5 { [] (Q -> (S && X(!R U T-> X(!R U (T && <> P))) U (R || [] (S && X(!R U T-> X(!R U (T && <> P))))))) }

	/* Response Chain -- S,T responds to P: */
	/* Globally */		ltl rc6 { [] (P -> <>(S && X<>T)) }
	/* Before R */		ltl rc7 { <>R -> (P -> (!R U (S && !R && X(!R U T))) U R) }
	/* After Q */		ltl rc8 { [] (Q -> [] (P -> (S && X<> T))) }
	/* Between Q and R */	ltl rc9 { [] ((Q && <>R)-> (P -> (!R U (S && !R && X(!R U T)))) U R) }
	/* After Q until R */	ltl rc10 { [] (Q -> (P -> (!R U (S && !R && X(!R U T)))U (R || [] (P -> (S && X<> T))))) }

	/* Constrained Chain -- S,T without Z responds to P: */
	/* Globally */		ltl cc1 { [] (P -> <>(S && !Z && X(!Z U T))) }
	/* Before R */		ltl cc2 { <>R -> (P -> (!R U (S && !R && !Z && X((!R && !Z U T)))) U R) }
	/* After Q */		ltl cc3 { [] (Q -> [] (P -> (S && !Z && X(!Z U T)))) }
	/* Between Q and R */	ltl cc4 { [] ((Q && <>R)-> (P -> (!R U (S && !R && !Z && X((!R && !Z U T)))) U R)) }
	/* After Q until R */	ltl cc5 { [] (Q -> (P -> (!R U (S && !R && !Z && X((!R && !Z U T)))) U (R || [] (P -> (S && !Z && X(!Z U T)))))) }

