// http://spinroot.com/spin/Doc/Exercises.html
// a simple model of a Petri Net

#define Place	byte	// assume at most 255 tokens per place

Place p1=1, p2, p3
Place p4=1, p5, p6

#define inp1(x)		(x>0) -> x--
#define inp2(x,y)	(x>0 && y>0) -> x--; y--
#define out1(x)		x++
#define out2(x,y)	x++; y++

init
{
  do
  :: inp1(p1)    -> out1(p2)	// t1
  :: inp2(p2,p4) -> out1(p3)	// t2
  :: inp1(p3)    -> out2(p1,p4)	// t3
  :: inp1(p4)    -> out1(p5)	// t4
  :: inp2(p1,p5) -> out1(p6)	// t5
  :: inp1(p6)    -> out2(p4,p1)	// t6
  od
}
