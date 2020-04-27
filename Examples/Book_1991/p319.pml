#define true	1
#define false	0

bool busy[3];

chan   up[3] = [1] of { byte };
chan down[3] = [1] of { byte };

mtype = { start, attention, data, stop }

proctype station(byte id; chan inp, out)
{	do
	:: inp?start ->
		atomic { !busy[id] -> busy[id] = true };
		out!attention;
		do
		:: inp?data -> out!data
		:: inp?stop -> break
		od;
		out!stop;
		busy[id] = false
	:: atomic { !busy[id] -> busy[id] = true };
		out!start;
		inp?attention;
		do
		:: out!data -> inp?data
		:: out!stop -> break
		od;
		inp?stop;
		busy[id] = false
	od
}

init {
	atomic {
		run station(0, up[2], down[2]);
		run station(1, up[0], down[0]);
		run station(2, up[1], down[1]);

		run station(0, down[0], up[0]);
		run station(1, down[1], up[1]);
		run station(2, down[2], up[2])
	}
}
