/* alternating bit - version with message loss */

#define MAX	3

mtype = { msg0, msg1, ack0, ack1 };

chan	sender  =[1] of { byte };
chan	receiver=[1] of { byte };

proctype Sender()
{	byte any;
again:
	do
	:: receiver!msg1;
		if
		:: sender?ack1 -> break
		:: sender?any /* lost */
		:: timeout    /* retransmit */
		fi
	od;
	do
	:: receiver!msg0;
		if
		:: sender?ack0 -> break
		:: sender?any /* lost */
		:: timeout    /* retransmit */
		fi
	od;
	goto again
}

proctype Receiver()
{	byte any;
again:
	do
	:: receiver?msg1 -> sender!ack1; break
	:: receiver?msg0 -> sender!ack0
	:: receiver?any /* lost */
	od;
P0:
	do
	:: receiver?msg0 -> sender!ack0; break
	:: receiver?msg1 -> sender!ack1
	:: receiver?any /* lost */
	od;
P1:
	goto again
}

init { atomic { run Sender(); run Receiver() } }

never {
	do
	:: skip	/* allow any time delay */
	:: receiver?[msg0] -> goto accept0
	:: receiver?[msg1] -> goto accept1
	od;
accept0:
	do
	:: !Receiver[2]@P0	/* n.b. new syntax of remote reference */
	od;
accept1:
	do
	:: !Receiver[2]@P1
	od
}
