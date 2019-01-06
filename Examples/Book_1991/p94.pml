byte state = 2;

proctype A() { (state == 1) -> state = 3 }

proctype B() { state = state - 1 }

/* added: */
init { run A(); run B() }
