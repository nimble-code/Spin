/* test execution priorities
   run this as:
	spin -p -g priorities
   requires Spin Version 2.5 or later
*/

int a[5];

proctype A()
{
	do
	:: printf("%d\n", _pid); a[_pid]++
	od
}

init {
	atomic {
		run A() priority 1;
		run A() priority 2;
		run A() priority 3;
		run A() priority 4;
}	}
