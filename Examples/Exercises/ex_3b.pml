// http://spinroot.com/spin/Doc/Exercises.html
// Peterson's algorithm, 1981

bool flag[2]
bool turn

active [2] proctype user()
{
	flag[_pid] = true
	turn = _pid
	(flag[1-_pid] == false || turn == 1-_pid)

crit:	skip	// critical section

	flag[_pid] = false
}
