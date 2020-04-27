/*
 * Models the Pathfinder scheduling algorithm and explains the
 * cause of the recurring reset problem during the mission on Mars
 *
 * there is a high priority process, that consumes
 * data produced by a low priority process.
 * data consumption and production happens under
 * the protection of a mutex lock
 * the mutex lock conflicts with the scheduling priorities
 * which can deadlock the system if high() starts up
 * while low() has the lock set
 * there are 12 reachable states in the full (non-reduced)
 * state space -- two of which are deadlock states
 * partial order reduction cannot be used here because of
 * the 'provided' clause that models the process priorities
 */

mtype = { free, busy, idle, waiting, running };

show mtype h_state = idle;
show mtype l_state = idle;
show mtype mutex = free;

active proctype high()	/* can run at any time */
{
end:	do
	:: h_state = waiting;
		atomic { mutex == free -> mutex = busy };
		h_state = running;

		/* critical section - consume data */

		atomic { h_state = idle; mutex = free }
	od
}

active proctype low() provided (h_state == idle) /* scheduling rule */
{
end:	do
	:: l_state = waiting;
		atomic { mutex == free -> mutex = busy};
		l_state = running;

		/* critical section - produce data */

		atomic { l_state = idle; mutex = free }
	od

}

