int tt = 80;
int pp = 45;

init {
	atomic {
	run receiver();
	}
}

proctype receiver() {
  int type = -1;
  int t = -1;
  int count = 10;
  int pp56 = 0;
  int pp10 = 0;

  do
  ::(count > 0) -> {
  pp = 20;
  if
    :: true -> {
        type = 0;
        pp = 56;
        pp56++;
        if
            :: true -> t = 11
            :: [prob = 35%] true -> t = 22
            :: [prob = pp] true -> t = 33
        fi;
        printf("now t is = %d", t);
    }
    :: [prob = 10%] true -> {type = 1; pp10++;}
    :: [prob = pp] true -> type = 2
    :: true -> type = 3
  fi;


   if
      :: true -> type = 11
      :: [prob = 35%] true -> type = 22
      :: [prob = pp] true -> type = 33
  fi;

  printf("now pp is = %d\n", pp);
  printf("now state is = %d\n", type);
  count = count - 1;
  }
  ::else -> break;
  od;
  printf("Total : pp10 = %d  pp56 = %d\n", pp10, pp56);

}