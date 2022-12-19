mtype = {s1, s2, s3};
int count = 0;
/* now define a normal chan */
chan a = [1] of { short };
/* now define a chan with 30% loss value */
chan [loss = 30%] b = [1] of { short };
/* now define a chan with 70% rely
value (or 30% loss) */
chan [rely = 70%] c = [1] of { short };

int pp = 70;

active proctype main() {
  mtype state = s1;
  count = pp - 10;
  /* send to a normal chan */
  a ! 1
  /* send to a 30% loss chan */
  b ! count;
  /* send to a chan with re-defined 10%
  loss */
  c ! [loss = 10%] 3;
  /* send to a chan with 70% reliability */
  c ! 2;
  /* send to a chan with re-defined 99% 
  reliability */
  c ! [rely = 99%] 4;
  /* send to a chan with re-defined loss 
  with count value */
  b ! [loss = count ] 1;
  if
    :: true -> state = s2; 
    /* 10% prob transition */ 
    :: [prob = 10%] true -> state = s3;
    /* dynamic prob transition */ 
    :: [prob = pp] true -> state = s3;
    /* for the others prob will be
       calculated as 100% - all
       specified probs */
    :: true -> state = s2; 
    :: true -> state = s3; 
  fi
  printf ("state = %d", state);
}
