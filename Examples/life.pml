// Conway's game of life

#define MAX	5
#define Board(x,y)	board[(which*MAX*MAX)+((x)*MAX)+(y)]
#define NewBoard(x,y)	board[((1-which)*MAX*MAX)+((x)*MAX)+(y)]

byte board[2*(MAX+1)*(MAX+1)];

int moveall;
int which;

inline print_board() {
	x = 0;
	do
	:: x < MAX ->
		y = 0; printf("|");
		do
		:: y < MAX ->
			if
			:: Board(x,y) -> printf("+")
			:: else -> printf(".")
			fi;
			y++
		:: else ->
			printf("|\n");
			break
		od;
		x++
	:: else ->
		printf(" -----\n");
		break
	od;
}

proctype cell(int x; int y)
{	int cnt, i, j;

	do
	:: 	d_step {
		moveall > 0 ->
		moveall--;
		cnt = 0;
		i = -1;
		do
		:: i <= 1 ->
			j = -1;
			do
			:: j <= 1 ->
				if
				:: (i != 0 || j != 0) && Board((x+i),(y+j)) -> cnt++
				:: else
				fi;
				j++;
			:: else ->
				break
			od;
			i++
		:: else ->
			break
		od;
		NewBoard(x,y) = Board(x,y);
		if
		:: Board(x,y) ->
// Any live cell with fewer than two live neighbours dies
// Any live cell with more than three live neighbours dies
// Any live cell with two or three live neighbours lives on to the next generation
			if
			:: cnt < 2 || cnt > 3 -> NewBoard(x,y) = 0
			:: else
			fi
		:: else ->
// Any dead cell with exactly three live neighbours becomes a live cell
			if
			:: cnt == 3 -> NewBoard(x,y) = 1
			:: else
			fi
		fi;
		};
		moveall == 0
	od
}

init {
	int x, y;
	NewBoard(2,1) = 1;
	NewBoard(2,2) = 1;
	NewBoard(2,3) = 1;

	atomic {
		x = 1;
		do
		:: x < MAX ->
			y = 1;
			do
			:: y < MAX -> run cell(x,y); y++
			:: else -> break
			od;
			x++
		:: else -> break
		od
	}

	do
	:: moveall == 0 ->
		which = 1 - which;
		print_board();
		moveall = (MAX-1)*(MAX-1)
	od
}
