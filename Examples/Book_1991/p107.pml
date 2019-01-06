mtype = { ack, nak, err, next, accept }

proctype transfer(chan inp, out, chin, chout)
{	byte o, i;

	inp?next(o);
	do
	:: chin?nak(i) -> out!accept(i); chout!ack(o)
	:: chin?ack(i) -> out!accept(i); inp?next(o); chout!ack(o)
	:: chin?err(i) -> chout!nak(o)
	od
}
init
{	chan AtoB = [1] of { byte, byte };
	chan BtoA = [1] of { byte, byte };
	chan Ain  = [2] of { byte, byte };
	chan Bin  = [2] of { byte, byte };
	chan Aout = [2] of { byte, byte };
	chan Bout = [2] of { byte, byte };

	atomic {
		run transfer(Ain, Aout, AtoB, BtoA);
		run transfer(Bin, Bout, BtoA, AtoB)
	};
	AtoB!err(0)
}
