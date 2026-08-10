chan a = [0] of { int };
chan b = [0] of { int };

active proctype p1() {
    a ! 1;
    b ? 1;
}

active proctype p2() {
    b ! 1;
    a ? 1;
}
