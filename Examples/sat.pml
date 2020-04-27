active proctype P() {
	bool a, b, c

	select(a: 0..1)
	select(b: 0..1)
	select(c: 0..1)

	assert(!((a ||  c) && (!a || !c) &&
		 (a || !b) && (!a ||  b) &&
		 (b || !c) && (!b || !c)))
}
