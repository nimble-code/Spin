/*
 *  a simple example of the use of inline's
 *  (requires Spin version 3.2 or later)
 *
 */

mtype = { msg0, msg1, ack0, ack1 };

chan sender = [1] of { mtype };
chan receiver = [1] of { mtype };

inline phase(msg, good_ack, bad_ack)
{
	do
	:: sender?good_ack -> break
	:: sender?bad_ack
	:: timeout -> 
		if
		:: receiver!msg;
		:: skip	/* lose message */
		fi;
	od
}

inline recv(cur_msg, cur_ack, lst_msg, lst_ack)
{
	do
	:: receiver?cur_msg -> sender!cur_ack; break /* accept */
	:: receiver?lst_msg -> sender!lst_ack
	od;
} 

active proctype Sender()
{
	do
	:: phase(msg1, ack1, ack0);
	   phase(msg0, ack0, ack1)
	od
}

active proctype Receiver()
{
	do
	:: recv(msg1, ack1, msg0, ack0);
	   recv(msg0, ack0, msg1, ack1)
	od
}
