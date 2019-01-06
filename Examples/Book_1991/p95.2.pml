proctype A(byte state; short set)
{	(state == 1) -> state = set
}

init { run A(1, 3) }
