#define MIN	9	/* first data message to send */
#define MAX	12	/* last  data message to send */
#define FILL	99	/* filler message */

mtype = { ack, nak, err }

proctype transfer(chan chin, chout)
{	byte o, i, last_i=MIN;

	o = MIN+1;
	do
	:: chin?nak(i) ->
		assert(i == last_i+1);
		chout!ack(o)
	:: chin?ack(i) ->
		if
		:: (o <  MAX) -> o = o+1	/* next */
		:: (o >= MAX) -> o = FILL	/* done */
		fi;
		chout!ack(o)
	:: chin?err(i) ->
		chout!nak(o)
	od
}

proctype channel(chan inp, out)
{	byte md, mt;
	do
	:: inp?mt,md ->
		if
		:: out!mt,md
		:: out!err,0
		fi
	od
}

init
{	chan AtoB = [1] of { byte, byte };
	chan BtoC = [1] of { byte, byte };
	chan CtoA = [1] of { byte, byte };
	atomic {
		run transfer(AtoB, BtoC);
		run channel(BtoC, CtoA);
		run transfer(CtoA, AtoB)
	};
	AtoB!err,0	/* start */
}
