// http://spinroot.com/spin/Doc/Exercises.html

#ifndef N
 #define N  2
#endif

init {
	chan dummy = [N] of { byte } // a message channel of N slots
	do
	:: dummy!85	// send byte value 85 to the channel
	:: dummy!170	// send byte value 170 to the channel
	od
}
