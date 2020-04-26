byte cnt;

/* the use of 'priority' tags enforces
   priority based scheduling
   it can be combined freely with provided clauses as well
   to finetune the scheduling choices
 */

active proctype medium() priority 5
{
	set_priority(0, 8);
	printf("medium %d - pid %d pr %d pr1 %d\n", _priority, _pid, get_priority(_pid), get_priority(0));
	cnt++
}

active proctype high() priority 10
{
	_priority = 9;
	printf("high %d\n", _priority);
	cnt++
}

active proctype low() priority 1
{
	/*
	 * can only execute if this is the highest
	 * priority process with executable statements
	 */

	assert(_priority == 1 && cnt == 2);
	printf("low %d\n", _priority);
}
