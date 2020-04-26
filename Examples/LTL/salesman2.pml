#define N	4
#ifndef MAX
	#define MAX	97
#endif

byte distance[N*N];
byte city, dest, tour, seen;
byte visited[N];	// shortest tour so far

#define Dist(a,b)	distance[((a)*N)+(b)]

//	(0) -- (1)
//	 | \__/ |
//	 | /  \ |
//	(2) -- (3)

inline travel2(dest) {

	(city != dest && tour <= MAX &&
	 (visited[dest] == 0 || tour + Dist(city,dest) < visited[dest])) ->

	tour = tour + Dist(city,dest)
	city = dest
	if
	:: !visited[city] ->
		visited[city] = tour
		printf("visit %d -- tour %d\n", city, tour)
		seen++
	:: else
	fi
}

init {
	Dist(0,1) = 20;	Dist(1,0) = 20
	Dist(0,2) = 42;	Dist(1,2) = 30
	Dist(0,3) = 35;	Dist(1,3) = 34

	Dist(2,0) = 42;	Dist(3,0) = 35
	Dist(2,1) = 30;	Dist(3,1) = 34
	Dist(2,3) = 12;	Dist(3,2) = 12

	// find shortest route to visit all nodes starting and ending at 0
	do
	:: select(dest : 0 .. (N-1)) -> travel2(dest)
	od

}

ltl p { [] ((seen < N) || (tour > MAX)) }

// exercises:
// 1.	change it so that the distance going from a higher
//	city number to a lower number is half that of going
//	the other way (downhill/uphill)
// 2.	change it to find the longest iso shortest tour
