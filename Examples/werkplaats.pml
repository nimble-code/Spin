#if 0
	given	2 jobs: j1, j2
	and	3 machines: m1, m2, m3
	
	job j1 needs:
		2 hours on m3, followed by 2 hours on m2, followed by 4 hours on m1
	job j2 needs:
		3 hours on m2, followed by 1 hour on m3
	
	Q1
	Can both jobs be completed in 7 hours or less?
	[A: no, j1 already needs 8 hours -- total time will be 8..11 hours]
	
	Q2
	What is the shortest time to complete both jobs?
	[A: 9]
	
	Q3
	Add a third job j3, which needs:
	2 hours on m2, followed by 3 hours on m1, followed by 2 hours on m3
	What is the shortest time to complete all three jobs?
	[A: 10]
	
	Q4
	Add another extra copy of machine m1
	What is the shortest time to complete all three jobs now?
	[A: 9]
#endif
 
#ifndef MAXTIME
	#define MAXTIME	9
#endif
 
byte m1[MAXTIME]	// records who's using m1 each hour
byte m2[MAXTIME]
byte m3[MAXTIME]
byte m4[MAXTIME]	// extra machine

bool j1_done
bool j2_done
bool j3_done

#define Find1(m,t,id) \
	do :: i < MAXTIME-t -> \
		if \
		:: atomic { !m[i] -> m[i] = id; i++; break } \
		:: else -> i++ \
		fi \
	od

#define Find2(m,t,id) \
	do :: i < MAXTIME-t -> \
		if \
		:: atomic { !m[i] && !m[i+1] -> \
			m[i] = id; m[i+1] = id; \
			i = i+2; break } \
		:: else -> i++ \
		fi \
	od

#define Find3(m,t,id) \
	do :: i < MAXTIME-t -> \
		if \
		:: atomic { !m[i] && !m[i+1] && !m[i+2] -> \
			m[i] = id; m[i+1] = id; m[i+2] = id; \
			i = i+3; break } \
		:: else -> i++ \
		fi \
	od

#define Find4(m,t,id) \
	do :: i < MAXTIME-t -> \
		if \
		:: atomic { !m[i] && !m[i+1] && !m[i+2] && !m[i+3] -> \
			m[i] = id; m[i+1] = id; m[i+2] = id; m[i+3] = id; \
			i = i+3; break } \
		:: else -> i++ \
		fi \
	od

active proctype j1()
{	int i

	Find2(m3, 8, 1) // 2 hours on m3; 8 remain
	Find2(m2, 6, 1) // 2 hours on m2; 6 remain

	if
	:: Find4(m1, 4, 1) // 4 hours on m1; 4 remain
//	:: Find4(m4, 4, 1)
	fi

	j1_done = 1
}

active proctype j2()
{	int i

	Find3(m2, 4, 2) // 3 hours on m2
	Find1(m3, 1, 2) // 1 hour  on m3
	j2_done = 1
}

active proctype j3()
{	int i

	Find2(m2, 7, 3) // 2 hours on m2
	Find3(m1, 5, 3) // 3 hours on m1
	Find2(m3, 2, 3) // 2 hours on m3
	j3_done = 1
}
 
never {
	do
	:: assert(!(j1_done && j2_done && j3_done))
	od
}
