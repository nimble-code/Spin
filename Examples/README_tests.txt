-- Updated for SPIN Version 6.3 --- May 2014 ---

To get comfortable with using Spin, perform the tests
test0 to test5 in the order listed, and check that you
get the same results.
The next four tests are to assess the effect of
partial order reductions.  In exhaustive mode, they
may not all be executable within the bounds of your
system - with reduction turned on, though, they should
all run as specified.
The last test checks the use of execution priorities
during random simulations.

	You can always check valid options of spin
	by typing (at command prompt $):
		$ spin --

	Similarly, you can check valid options of
	the compiled verifiers by typing:
		$ pan --

test 0	check that spin exists, is executable, and is
	the version that you expect

	$ spin -V
	Spin Version 6.0.0 -- 18 September 2010

test 1	check that you can run a simulation

	$ spin hello.pml
		passed first test!
	1 process created

	or without the default indenting of output:

	$ spin -T hello.pml
	passed first test!
	1 process created

test 2	a basic reachability check (safety)

	$ spin -a loops.pml            # generate c-verifier
	$ cc -DNOREDUCE -o pan pan.c # no reduction (test)
	$ ./pan                        # default run
	hint: this search is more efficient if pan.c is compiled -DSAFETY

	(Spin Version 6.0.0 -- 18 September 2010)

	Full statespace search for:
	        never-claim             - (none specified)
	        assertion violations    +
	        acceptance   cycles     - (not selected)
	        invalid endstates       +
	
	State-vector 12 byte, depth reached 11, errors: 0
	      15 states, stored
	       4 states, matched
	      19 transitions (= stored+matched)
	       0 atomic steps
	hash conflicts: 0 (resolved)
	
	2.501     memory usage (Mbyte)

	unreached in proctype loop
        	line 12, state 12, "-end-"
        	(1 of 12 states)

	pan: elapsed time 0 seconds

test 3	cycle detection check (liveness):

	$ ./pan -a		# search for acceptance cycles
	pan: acceptance cycle (at depth 0)
	pan: wrote loops.pml.trail
	(Spin Version 6.0.0 -- 18 September 2010)
	Warning: Search not completed
	
	Full statespace search for:
	        never-claim             - (none specified)
	        assertion violations    +
>	        acceptance   cycles     + (fairness disabled)
	        invalid endstates       +
	
	State-vector 12 byte, depth reached 11, errors: 1
	      13 states, stored (15 visited)
	       2 states, matched
	      17 transitions (= visited+matched)
	       0 atomic steps
	hash conflicts: 0 (resolved)
	
	2.501     memory usage (Mbyte)

	pan: elapsed time 0.015 seconds
	pan: rate      1000 states/second

test 4	guided simulation check (playback the error trail found in test 3)

	$ spin -t -p loops.pml	# guided simulation for the error-cycle
	  <<<<<START OF CYCLE>>>>>
	  1:    proc  0 (loop) loops.pml:5 (state 1)       [a = ((a+1)%3)]
	  2:    proc  0 (loop) loops.pml:7 (state 2)       [b = (2*a)]
	  3:    proc  0 (loop) loops.pml:7 (state 3)       [(1)]
	  4:    proc  0 (loop) loops.pml:10 (state 8)       [b = (b-1)]
	  5:    proc  0 (loop) loops.pml:5 (state 1)       [a = ((a+1)%3)]
	  6:    proc  0 (loop) loops.pml:7 (state 2)       [b = (2*a)]
	  7:    proc  0 (loop) loops.pml:7 (state 3)       [(1)]
	  8:    proc  0 (loop) loops.pml:10 (state 8)       [b = (b-1)]
	  9:    proc  0 (loop) loops.pml:5 (state 1)       [a = ((a+1)%3)]
	 10:    proc  0 (loop) loops.pml:8 (state 4)       [b = (2*a)]
	 11:    proc  0 (loop) loops.pml:8 (state 5)       [(1)]
	spin: loops.pml:10, Error: value (-1->255 (8)) truncated in assignment
	 12:    proc  0 (loop) loops.pml:10 (state 8)       [b = (b-1)]
	spin: trail ends after 12 steps
	#processes: 1
	 12:    proc  0 (loop) loops.pml:4 (state 9)
	1 process created

test 5	try to find a cycle that avoids the progress labels (there are none)

	$ cc -DNP -DNOREDUCE -o pan pan.c # add support for non-progress
	$ ./pan -l		# search for non-progress cycles

	(Spin Version 6.0.0 -- 18 September 2010)
	
	Full statespace search for:
	        never claim             +
	        assertion violations    + (if within scope of claim)
	        non-progress cycles     + (fairness disabled)
	        invalid end states      - (disabled by never claim)
	
	State-vector 16 byte, depth reached 23, errors: 0
	       27 states, stored (39 visited)
	       28 states, matched
	       67 transitions (= visited+matched)
	        0 atomic steps
	hash conflicts:         0 (resolved)
	
	2.501           memory usage (Mbyte)
	
	unreached in proctype loop
	        line 12, state 12, "-end-"
	        (1 of 12 states)
	
	pan: elapsed time 0 seconds

test 6:	check partial order reduction algorithm -- first disable it

	$ spin -a leader0.pml	# note leader0.pml not leader.pml
	$ cc -DSAFETY -DNOREDUCE -DNOCLAIM -o pan pan.c	# safety only
	$ ./pan -c0 -n                # exhaustive, -c0 = ignore errors
	(Spin Version 6.0.0 -- 18 September 2010)

	Full statespace search for:
	        never claim             - (not selected)
	        assertion violations    +
	        cycle checks            - (disabled by -DSAFETY)
	        invalid end states      +
	
	State-vector 196 byte, depth reached 108, errors: 0
	    15779 states, stored
	    42402 states, matched
	    58181 transitions (= stored+matched)
	       12 atomic steps
	hash conflicts:       440 (resolved)
	
	Stats on memory usage (in Megabytes):
	3.010           equivalent memory usage for states (stored*(State-vector + overhead))
	2.731           actual memory usage for states (compression: 90.73%)
	                state-vector as stored = 177 byte + 4 byte overhead
	2.000           memory used for hash table (-w19)
	0.267           memory used for DFS stack (-m10000)
	0.094           memory lost to fragmentation
	4.904           total actual memory usage
	
	pan: elapsed time 0.125 seconds
	pan: rate    126232 states/second

test 6b: now leave p.o. reduction enabled (i.e., do not disable it)

	$ cc -DSAFETY -DNOCLAIM -o pan pan.c  # safety only, reduced search
	$ ./pan -c0 -n                # -n = no dead code listing

	(Spin Version 6.0.0 -- 18 September 2010)
	        + Partial Order Reduction
	
	Full statespace search for:
	        never claim             - (not selected)
	        assertion violations    +
	        cycle checks            - (disabled by -DSAFETY)
	        invalid end states      +
	
	State-vector 196 byte, depth reached 108, errors: 0
	       97 states, stored
	        0 states, matched
	       97 transitions (= stored+matched)
	       12 atomic steps
	hash conflicts:         0 (resolved)
	
	2.501           memory usage (Mbyte)
	
	pan: elapsed time 0 seconds

	If compiled as above, the results should match the results from the table below. 
	The numbers in the first two columns of the table should match precisely.  
	The numbers in the third column should match approximately (how well it matches
	depends only on the properties of the C-compiler and the speed of the hardware
	you use to run the tests.)
	The first line for each test is for the exhaustive run, the second line is for
	the default run using partial order reduction.
	The times given are for a 2.4GHz dual-core Intel PC, with 2 GB of memory.

	States Stored	Transitions	Memory Used	Time (s)
leader0
	S=   15779      T=   58181	M= 4.904 Mb	t= 0.125
	S=      97      T=      97	M= 2.501 Mb	t= <0.1

snoopy
	S=   61619	T=  211398	M= 8.03 Mb	t= 0.328
	S=    9343	T=   12706	M= 3.38 Mb	t= 0.03

pftp
	S=  144813	T=  397948	M= 18.97 Mb	t= 0.79
	S=   47356	T=   64970	M=  8.07 Mb	t= 0.14

sort
	S=  107713	T=  512419	M= 18.87 Mb	t= 1.08
	S=     135	T=     135	M=  2.50 Mb	t= <0.1


test 7	check random number generator

	$ spin -o6 -p -g -u10000 priorities.pml	# runs 10000 steps
	# the -o6 restores the pre-release 6.2 functionality of priorities
	# for more info: http://spinroot.com/spin/multicore/priority.html
	....
	depth-limit (-u10000 steps) reached
	#processes: 5
	                a[0] = 0
	                a[1] = 334
	                a[2] = 677
	                a[3] = 994
	                a[4] = 1327
	10000:  proc  4 (A) line  11 "priorities" (state 3)
	10000:  proc  3 (A) line  12 "priorities" (state 2)
	10000:  proc  2 (A) line  14 "priorities" (state 4)
	10000:  proc  1 (A) line  11 "priorities" (state 3)
	10000:  proc  0 (:init:) line  22 "priorities" (state 6) <valid end state>
	5 processes created

	The numbers in the array should tend to the ratio
	1:2:3:4 if the random number generator works properly.
	array index 0 remains unused (it's the pid of the init
	process)

test 8	test the generation of never claims from LTL formulae:

	$ spin -f "[] ( p U ( <> q ))"

	never {    /* [] ( p U ( <> q )) */
	T0_init:
	        if
	        :: ((q)) -> goto accept_S9
	        :: (1) -> goto T0_init
	        fi;
	accept_S9:
	        if
	        :: (1) -> goto T0_init
	        fi;
	}

Note: ltl formula are more conveniently specified inline
when using Spin version 6 or later.
Explore the use of inline ltl formula in the 16 examples
in the LTL sub-directory

There are additional examples of Promela models
in this directory as well, not covered by the tests above.
The tests used:
	hello.pml
	leader0.pml
	loops.pml
	priorities.pml

Other examples include:
	abp.pml
	cambridge.pml
	dtp.pml
	eratosthenes.pml
	for_example.pml
	for_select_example.pml
	hajek.pml
	leader_trace.pml
	life.pml
	manna_pnueli.pml
	pathfinder.pml
	peterson.pml
	rtos1.pml
	sat.pml
	snoopy.pml
	sort.pml
	welfare.pml
	werkplaats.pml
	wordcount.pml

The file pathfinder.pml, for instance, illustrates
the use of 'provided' clauses (using as inspiration
the bug in the control software of the Mars pathfinder
that struck an otherwise perfect mission in July 1997)
The file rtos1.pml illustrates the use of priorities.
The file life.pml does a simple encoding of Conway's
game of life. File sat.pml shows a satisfiability problem.

The 10 files in the Exercises sub-directory
include all exercises and examples from:
	http://spinroot.com/spin/Man/Exercises.html

Last Updated: 11 May 2014
