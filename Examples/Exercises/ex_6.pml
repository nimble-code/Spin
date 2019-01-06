// http://spinroot.com/spin/Doc/Exercises.html

#define MaxSeq	3
#define inc(x)	x = (x+1)%(MaxSeq+1)

mtype = { none, red, white, blue }	// Wolper's test

bool sent_r, sent_b		// initialized to false
bool received_r, received_b	// initialized to false

chan q[2] = [MaxSeq] of { mtype, byte, byte }
chan source = [0] of { mtype }

active [2] proctype p5()
{	byte NextFrame, AckExp, FrameExp, r, s, nbuf, i
	byte  frames[MaxSeq+1]
	mtype ball = none
	chan  inp, out

	inp = q[_pid]
	out = q[1-_pid]

	do
	:: nbuf < MaxSeq ->
		nbuf++
		if
		:: _pid%2 -> source?ball
		:: else
		fi
		frames[NextFrame] = ball
		out!ball, NextFrame, (FrameExp + MaxSeq) % (MaxSeq + 1)
		printf("MSC: nbuf: %d\n", nbuf)
		inc(NextFrame)
	:: inp?ball,r,s ->
		if
		:: r == FrameExp ->
			printf("MSC: accept %e %d\n", ball, r)
			if
			:: !(_pid%2) && ball == red -> received_r = true
			:: !(_pid%2) && ball == blue -> received_b = true
			:: else
			fi
			inc(FrameExp)
		:: else ->
			printf("MSC: reject\n")
		fi
	 	do
		:: ((AckExp <= s) && (s <  NextFrame)) ||
		   ((AckExp <= s) && (NextFrame <  AckExp)) ||
		   ((s <  NextFrame) && (NextFrame <  AckExp)) ->
			nbuf--
			printf("MSC: nbuf: %d\n", nbuf)
			inc(AckExp)
		:: else ->
			printf("MSC: %d %d %d\n", AckExp, s, NextFrame)
			break
		od
	:: timeout ->
		NextFrame = AckExp
		printf("MSC: timeout\n")
		i = 1
		do
		:: i <= nbuf ->
			if
			:: _pid%2 -> ball = frames[NextFrame]
			:: else
			fi	
			out!ball, NextFrame, (FrameExp + MaxSeq) % (MaxSeq + 1)
			inc(NextFrame)
			i++
		:: else ->
			break
		od
	od
}

active proctype Source()
{
	do
	:: source!white
	:: source!red ->
		sent_r = true
		break
	od
	do
	:: source!white
	:: source!blue ->
		sent_b = true
		break
	od
end:	do
	:: source!white
	od
}

ltl p1 { (<> sent_r -> <> (received_r && !received_b)) }
