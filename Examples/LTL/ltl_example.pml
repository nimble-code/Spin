chan q; int a;

ltl c6	{ [] ( (len(q) < 2) -> (len(q) > 0) ) }

init { printf("hello world\n") }
