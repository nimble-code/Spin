// clang-format off
/***** spin: main.c *****/

/*
 * This file is part of the public release of Spin. It is subject to the
 * terms in the LICENSE file that is included in this source directory.
 * Tool documentation is available at http://spinroot.com
 */

#include <stdlib.h>
#include <assert.h>
#include "spin.h"
#include "version.h"
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <signal.h>
#include <time.h>
#ifdef PC
 #include <io.h>
#else
 #include <unistd.h>
#endif
#include "y.tab.h"

#include <argp.h>

extern int	DstepStart, lineno, tl_terse;
extern FILE	*yyin, *yyout, *tl_out;
extern Symbol	*context;
extern char	*claimproc;
extern void	repro_src(void);
extern void	qhide(int);
extern char	CurScope[MAXSCOPESZ];
extern short	has_provided, has_code, has_ltl, has_accept;
extern int	realread, buzzed;
extern void	ana_src(int, int);
extern void	putprelude(void);

static void	add_comptime(char *);
static void	add_runtime(char *);

Symbol	*Fname, *oFname;

static char doc[] = SpinVersion;
// The arguments that get printed after the program, ex: `spin [OPTIONS...] ARGUMENTS`
static char args_doc[] = "FILE";

int	Etimeouts;	/* nr timeouts in program */
int	Ntimeouts;	/* nr timeouts in never claim */
int	analyze, columns, dumptab, has_remote, has_remvar;
int	interactive, jumpsteps, m_loss, nr_errs, cutoff;
int	s_trail, ntrail, verbose, xspin, notabs, rvopt;
int	no_print, no_wrapup, Caccess, limited_vis, like_java;
int	separate;	/* separate compilation */
int	export_ast;	/* pangen5.c */
int	norecompile;	/* main.c */
int	old_scope_rules;	/* use pre 5.3.0 rules */
int	old_priority_rules;	/* use pre 6.2.0 rules */
int	product, Strict;
short	replay;

int	merger = 1, deadvar = 1, implied_semis = 1;
int	ccache = 0; /* oyvind teig: 5.2.0 case caching off by default */

static int preprocessonly, SeedUsed, itsr, itsr_n, sw_or_bt;
static int seedy;	/* be verbose about chosen seed */
static int inlineonly;	/* show inlined code */
static int dataflow = 1;

#if 0
meaning of flags on verbose:
	1	-g global variable values
	2	-l local variable values
	4	-p all process actions
	8	-r receives
	16	-s sends
	32	-v verbose
	64	-w very verbose
#endif

static char	Operator[] = "operator: ";
static char	Keyword[]  = "keyword: ";
static char	Function[] = "function-name: ";
static char	**add_ltl  = (char **) 0;
static char	**ltl_file = (char **) 0;
static char	**nvr_file = (char **) 0;
static char	*ltl_claims = (char *) 0;
static char	*pan_runtime = "";
static char	*pan_comptime = "";
static char	*formula = NULL;
static FILE	*fd_ltl = (FILE *) 0;
static char	*PreArg[64];
static int	PreCnt = 0;
static char	out1[64];

void pre_arg_append(char* arg) {
  assert(PreCnt < sizeof(PreArg));
  PreArg[PreCnt++] = arg;
}

char	**trailfilename;	/* new option 'k' */

void	explain(int);

#ifndef CPP
	/* to use visual C++:
		#define CPP	"cl -E/E"
	   or call spin as:	spin -P"CL -E/E"

	   on OS2:
		#define CPP	"icc -E/Pd+ -E/Q+"
	   or call spin as:	spin -P"icc -E/Pd+ -E/Q+"
	   make sure the -E arg is always at the end,
	   in each case, because the command line
	   can later be truncated at that point
	*/
 #if 1
	#define CPP	"gcc -std=gnu99 -Wno-unknown-warning-option -Wformat-overflow=0 -E -x c"
	/* if gcc-4 is available, this setting is modified below */
 #else
	#if defined(PC) || defined(MAC)
		#define CPP	"gcc -std=gnu99 -E -x c"
	#else
		#ifdef SOLARIS
			#define CPP	"/usr/ccs/lib/cpp"
		#else
			#define CPP	"cpp"	/* sometimes: "/lib/cpp" */
		#endif
	#endif
 #endif
#endif

static char	PreProc[512];
extern int	depth; /* at least some steps were made */

int
WhatSeed(void)
{
	return SeedUsed;
}

void
final_fiddle(void)
{	char *has_a, *has_l, *has_f;

	/* no -a or -l but has_accept: add -a */
	/* no -a or -l in pan_runtime: add -DSAFETY to pan_comptime */
	/* -a or -l but no -f then add -DNOFAIR */

	has_a = strstr(pan_runtime, "-a");
	has_l = strstr(pan_runtime, "-l");
	has_f = strstr(pan_runtime, "-f");

	if (!has_l && !has_a && strstr(pan_comptime, "-DNP"))
	{	add_runtime("-l");
		has_l = strstr(pan_runtime, "-l");
	}

	if (!has_a && !has_l
	&&  !strstr(pan_comptime, "-DSAFETY"))
	{	if (has_accept
		&& !strstr(pan_comptime, "-DBFS")
		&& !strstr(pan_comptime, "-DNOCLAIM"))
		{	add_runtime("-a");
			has_a = pan_runtime;
		} else
		{	add_comptime("-DSAFETY");
	}	}

	if ((has_a || has_l) && !has_f
	&&  !strstr(pan_comptime, "-DNOFAIR"))
	{	add_comptime("-DNOFAIR");
	}
}

static int
change_param(char *t, char *what, int range, int bottom)
{	char *ptr;
	int v;

	assert(range < 1000 && range > 0);
	if ((ptr = strstr(t, what)) != NULL)
	{	ptr += strlen(what);
		if (!isdigit((int) *ptr))
		{	return 0;
		}
		v = atoi(ptr) + 1;	/* was: v = (atoi(ptr)+1)%range */
		if (v >= range)
		{	v = bottom;
		}
		if (v >= 100)
		{	*ptr++ = '0' + (v/100); v %= 100;
			*ptr++ = '0' + (v/10);
			*ptr   = '0' + (v%10);
		} else if (v >= 10)
		{	*ptr++ = '0' + (v/10);
			*ptr++ = '0' + (v%10);
			*ptr   = ' ';
		} else
		{	*ptr++ = '0' + v;
			*ptr++ = ' ';
			*ptr   = ' ';
	}	}
	return 1;
}

static void
change_rs(char *t)
{	char *ptr;
	int cnt = 0;
	long v;

	if ((ptr = strstr(t, "-RS")) != NULL)
	{	ptr += 3;
		/* room for at least 10 digits */
		v = Rand()%1000000000L;
		while (v/10 > 0)
		{	*ptr++ = '0' + v%10;
			v /= 10;
			cnt++;
		}
		*ptr++ = '0' + v;
		cnt++;
		while (cnt++ < 10)
		{	*ptr++ = ' ';
	}	}
}

int
omit_str(char *in, char *s)
{	char *ptr = strstr(in, s);
	int i, nr = -1;

	if (ptr)
	{	for (i = 0; i < (int) strlen(s); i++)
		{	*ptr++ = ' ';
		}
		if (isdigit((int) *ptr))
		{	nr = atoi(ptr);
			while (isdigit((int) *ptr))
			{	*ptr++ = ' ';
	}	}	}
	return nr;
}

void
string_trim(char *t)
{	int n = strlen(t) - 1;

	while (n > 0 && t[n] == ' ')
	{	t[n--] = '\0';
	}
}

int
e_system(int v, const char *s)
{	static int count = 1;

	/* v == 0 : checks to find non-linked version of gcc */
	/* v == 1 : all other commands */
	/* v == 2 : preprocessing the promela input */

	if (v == 1)
	{	if (verbose&(32|64))	/* -v or -w */
		{	printf("cmd%02d: %s\n", count++, s);
			fflush(stdout);
		}
		if (verbose&64)		/* only -w */
		{	return 0;	/* suppress the call to system(s) */
	}	}
	return system(s);
}

void
alldone(int estatus)
{	char *ptr;
#if defined(WIN32) || defined(WIN64)
	struct _stat x;
#else
	struct stat x;
#endif
	if (preprocessonly == 0 &&  strlen(out1) > 0)
	{	(void) unlink((const char *) out1);
	}

	(void) unlink(TMP_FILE1);
	(void) unlink(TMP_FILE2);

	if (!buzzed && seedy && !analyze && !export_ast
	&& !s_trail && !preprocessonly && depth > 0)
	{	printf("seed used: %d\n", SeedUsed);
	}

	if (!buzzed && xspin && (analyze || s_trail))
	{	if (estatus)
		{	printf("spin: %d error(s) - aborting\n",
				estatus);
		} else
		{	printf("Exit-Status 0\n");
	}	}

	if (buzzed && replay && !has_code && !estatus)
	{	extern QH *qh_lst;
		QH *j;
		int i;

		pan_runtime = (char *) emalloc(2048);	/* more than enough */
		sprintf(pan_runtime, "-n%d ", SeedUsed);
		if (jumpsteps)
		{	sprintf(&pan_runtime[strlen(pan_runtime)], "-j%d ", jumpsteps);
		}
		if (trailfilename)
		{	sprintf(&pan_runtime[strlen(pan_runtime)], "-k%s ", *trailfilename);
		}
		if (cutoff)
		{	sprintf(&pan_runtime[strlen(pan_runtime)], "-u%d ", cutoff);
		}
		for (i = 0; i < PreCnt; i++)
		{	strcat(pan_runtime, PreArg[i]);
			strcat(pan_runtime, " ");
		}
		for (j = qh_lst; j; j = j->nxt)
		{	sprintf(&pan_runtime[strlen(pan_runtime)], "-q%d ", j->n);
		}
		if (strcmp(PreProc, CPP) != 0)
		{	sprintf(&pan_runtime[strlen(pan_runtime)], "\"-P%s\" ", PreProc);
		}
		/* -oN options 1..5 are ignored in simulations */
		if (old_priority_rules) strcat(pan_runtime, "-o6 ");
		if (!implied_semis)  strcat(pan_runtime, "-o7 ");
		if (no_print)        strcat(pan_runtime, "-b ");
		if (no_wrapup)       strcat(pan_runtime, "-B ");
		if (columns == 1)    strcat(pan_runtime, "-c ");
		if (columns == 2)    strcat(pan_runtime, "-M ");
		if (seedy == 1)      strcat(pan_runtime, "-h ");
		if (like_java == 1)  strcat(pan_runtime, "-J ");
		if (old_scope_rules) strcat(pan_runtime, "-O ");
		if (notabs)          strcat(pan_runtime, "-T ");
		if (verbose&1)       strcat(pan_runtime, "-g ");
		if (verbose&2)       strcat(pan_runtime, "-l ");
		if (verbose&4)       strcat(pan_runtime, "-p ");
		if (verbose&8)       strcat(pan_runtime, "-r ");
		if (verbose&16)      strcat(pan_runtime, "-s ");
		if (verbose&32)      strcat(pan_runtime, "-v ");
		if (verbose&64)      strcat(pan_runtime, "-w ");
		if (m_loss)          strcat(pan_runtime, "-m ");

		char *tmp = (char *) emalloc(strlen("spin -t") +
				strlen(pan_runtime) + strlen(Fname->name) + 8);

		sprintf(tmp, "spin -t %s %s", pan_runtime, Fname->name);
		estatus = e_system(1, tmp);	/* replay */
		exit(estatus);	/* replay without c_code */
	}

	if (buzzed && (!replay || has_code) && !estatus)
	{	char *tmp, *tmp2 = NULL, *P_X;
		char *C_X = (buzzed == 2) ? "-O" : "";

		if (replay && strlen(pan_comptime) == 0)
		{
#if defined(WIN32) || defined(WIN64)
			P_X = "pan";
#else
			P_X = "./pan";
#endif
			if (stat(P_X, (struct stat *)&x) < 0)
			{	goto recompile;	/* no executable pan for replay */
			}
			tmp = (char *) emalloc(8 + strlen(P_X) + strlen(pan_runtime) +4);
			/* the final +4 is too allow adding " &" in some cases */
			sprintf(tmp, "%s %s", P_X, pan_runtime);
			goto runit;
		}
#if defined(WIN32) || defined(WIN64)
		P_X = "-o pan pan.c && pan";
#else
		P_X = "-o pan pan.c && ./pan";
#endif
		/* swarm and biterate randomization additions */
		if (!replay && itsr)	/* iterative search refinement */
		{	if (!strstr(pan_comptime, "-DBITSTATE"))
			{	add_comptime("-DBITSTATE");
			}
			if (!strstr(pan_comptime, "-DPUTPID"))
			{	add_comptime("-DPUTPID");
			}
			if (!strstr(pan_comptime, "-DT_RAND")
			&&  !strstr(pan_comptime, "-DT_REVERSE"))
			{	add_runtime("-T0  ");	/* controls t_reverse */
			}
			if (!strstr(pan_runtime, "-P")	/* runtime flag */
			||   pan_runtime[2] < '0'
			||   pan_runtime[2] > '1') /* no -P0 or -P1 */
			{	add_runtime("-P0  ");	/* controls p_reverse */
			}
			if (!strstr(pan_runtime, "-w"))
			{	add_runtime("-w18 ");	/* -w18 = 256K */
			} else
			{	char nv[32];
				int x;
				x = omit_str(pan_runtime, "-w");
				if (x >= 0)
				{	sprintf(nv, "-w%d  ", x);
					add_runtime(nv); /* added spaces */
			}	}
			if (!strstr(pan_runtime, "-h"))
			{	add_runtime("-h0  ");	/* 0..499 */
				/* leave 2 spaces for increments up to -h499 */
			} else if (!strstr(pan_runtime, "-hash"))
			{	char nv[32];
				int x;
				x = omit_str(pan_runtime, "-h");
				if (x >= 0)
				{	sprintf(nv, "-h%d  ", x%500);
					add_runtime(nv); /* added spaces */
			}	}
			if (!strstr(pan_runtime, "-k"))
			{	add_runtime("-k1  ");	/* 1..3 */
			} else
			{	char nv[32];
				int x;
				x = omit_str(pan_runtime, "-k");
				if (x >= 0)
				{	sprintf(nv, "-k%d  ", x%4);
					add_runtime(nv); /* added spaces */
			}	}
			if (strstr(pan_runtime, "-p_rotate"))
			{	char nv[32];
				int x;
				x = omit_str(pan_runtime, "-p_rotate");
				if (x < 0)
				{	x = 0;
				}
				sprintf(nv, "-p_rotate%d  ", x%256);
				add_runtime(nv); /* added spaces */
			} else if (strstr(pan_runtime, "-p_permute") == 0)
			{	add_runtime("-p_rotate0  ");
			}
			if (strstr(pan_runtime, "-RS"))
			{	(void) omit_str(pan_runtime, "-RS");
			}
			/* need room for at least 10 digits */
			add_runtime("-RS1234567890 ");
			change_rs(pan_runtime);
		}
recompile:
		if (strstr(PreProc, "cpp"))	/* unix/linux */
		{	strcpy(PreProc, "gcc");	/* need compiler */
		} else if ((tmp = strstr(PreProc, "-E")) != NULL)
		{	*tmp = '\0'; /* strip preprocessing flags */
		}

		final_fiddle();
		tmp = (char *) emalloc(8 +	/* account for alignment */
				strlen(PreProc) +
				strlen(C_X) +
				strlen(pan_comptime) +
				strlen(P_X) +
				strlen(pan_runtime) +
				strlen(" -p_reverse & "));
		tmp2 = tmp;

		/* P_X ends with " && ./pan " */
		sprintf(tmp, "%s %s %s %s %s",
			PreProc, C_X, pan_comptime, P_X, pan_runtime);

		if (!replay)
		{	if (itsr < 0)		/* swarm only */
			{	strcat(tmp, " &"); /* after ./pan */
				itsr = -itsr;	/* now same as biterate */
			}
			/* do compilation first
			 * split cc command from run command
			 * leave cc in tmp, and set tmp2 to run
			 */
			if ((ptr = strstr(tmp, " && ")) != NULL)
			{	tmp2 = ptr + 4;	/* first run */
				*ptr = '\0';
		}	}

		if (has_ltl)
		{	(void) unlink("_spin_nvr.tmp");
		}

		if (!norecompile)
		{	/* make sure that if compilation fails we do not continue */
#ifdef PC
			(void) unlink("./pan.exe");
#else
			(void) unlink("./pan");
#endif
		}
runit:
		if (norecompile && tmp != tmp2)
		{	estatus = 0;
		} else
		{	estatus = e_system(1, tmp);	/* compile or run */
		}
		if (replay || estatus < 0)
		{	goto skipahead;
		}
		/* !replay */
		if (itsr == 0 && !sw_or_bt)			/* single run */
		{	estatus = e_system(1, tmp2);
		} else if (itsr > 0)	/* iterative search refinement */
		{	int is_swarm = 0;
			if (tmp2 != tmp)	/* swarm: did only compilation so far */
			{	tmp = tmp2;	/* now we point to the run command */
				estatus = e_system(1, tmp);	/* first run */
				itsr--;
			}
			itsr--;			/* count down */

			/* the following are added back randomly later */
			(void) omit_str(tmp, "-p_reverse");	/* replaced by spaces */
			(void) omit_str(tmp, "-p_normal");

			if (strstr(tmp, " &") != NULL)
			{	(void) omit_str(tmp, " &");
				is_swarm = 1;
			}

			/* increase -w every itsr_n-th run */
			if ((itsr_n > 0 && (itsr == 0 || (itsr%itsr_n) != 0))
			||  (change_param(tmp, "-w", 36, 18) >= 0))	/* max 4G bit statespace */
			{	(void) change_param(tmp, "-h", 500, 0);	/* hash function 0.499 */
				(void) change_param(tmp, "-p_rotate", 256, 0); /* if defined */
				(void) change_param(tmp, "-k", 4, 1);	/* nr bits per state 0->1,2,3 */
				(void) change_param(tmp, "-T", 2, 0);	/* with or without t_reverse*/
				(void) change_param(tmp, "-P", 2, 0);	/* -P 0..1 != p_reverse */
				change_rs(tmp);			/* change random seed */
				string_trim(tmp);
				if (rand()%5 == 0)		/* 20% of all runs */
				{	strcat(tmp, " -p_reverse ");
					/* at end, so this overrides -p_rotateN, if there */
					/* but -P0..1 disable this in 50% of the cases */
					/* so its really activated in 10% of all runs */
				} else if (rand()%6 == 0) /* override p_rotate and p_reverse */
				{	strcat(tmp, " -p_normal ");
				}
				if (is_swarm)
				{	strcat(tmp, " &");
				}
				goto runit;
		}	}
skipahead:
		(void) unlink("pan.b");
		(void) unlink("pan.c");
		(void) unlink("pan.h");
		(void) unlink("pan.m");
		(void) unlink("pan.p");
		(void) unlink("pan.t");
	}
	exit(estatus);
}
#if 0
	-P0	normal active process creation
	-P1	reversed order for *active* process creation != p_reverse

	-T0	normal transition exploration
	-T1	reversed order of transition exploration

	-DP_RAND	(random starting point +- -DP_REVERSE)
	-DPERMUTED	(also enables -p_rotateN and -p_reverse)
	-DP_REVERSE	(same as -DPERMUTED with -p_reverse, but 7% faster)

	-DT_RAND	(random starting point -- optionally with -T0..1)
	-DT_REVERSE	(superseded by -T0..1 options)

	 -hash generates new hash polynomial for -h0

	permutation modes:
	 -permuted (adds -DPERMUTED) -- this is also the default with -swarm
	 -t_reverse (same as -T1)
	 -p_reverse (similar to -P1)
	 -p_rotateN
	 -p_normal

	less useful would be (since there is less non-determinism in transitions):
		-t_rotateN -- a controlled version of -DT_RAND

	compiling with -DPERMUTED enables a number of new runtime options,
	that -swarmN,M will also exploit:
		-p_permute (default)
		-p_rotateN
		-p_reverse
#endif

void
preprocess(char *a, char *b, int a_tmp)
{	char precmd[1024], cmd[2048];
	int i;
#ifdef PC
	/* gcc is sometimes a symbolic link to gcc-4
	   that does not work well in cygwin, so we try
	   to use the actual executable that is used.
	   the code below assumes we are on a cygwin-like system
	 */
	if (strncmp(PreProc, "gcc ", strlen("gcc ")) == 0)
	{	if (e_system(0, "gcc-4 --version > pan.pre 2>&1") == 0)
		{	strcpy(PreProc, "gcc-4 -std=gnu99 -Wno-unknown-warning-option -Wformat-overflow=0 -E -x c");
		} else if (e_system(0, "gcc-3 --version > pan.pre 2>&1") == 0)
		{	strcpy(PreProc, "gcc-3 -std=gnu99 -Wno-unknown-warning-option -Wformat-overflow=0 -E -x c");
	}	}
#endif

	assert(strlen(PreProc) < sizeof(precmd));
	strcpy(precmd, PreProc);
	for (i = 0; i < PreCnt; i++)
	{	strcat(precmd, " ");
		strcat(precmd, PreArg[i]);
	}
	if (strlen(precmd) > sizeof(precmd))
	{	fprintf(stdout, "spin: too many -D args, aborting\n");
		alldone(1);
	}
	sprintf(cmd, "%s \"%s\" > \"%s\"", precmd, a, b);
	if (e_system(2, (const char *)cmd))	/* preprocessing step */
	{	(void) unlink((const char *) b);
		if (a_tmp) (void) unlink((const char *) a);
		fprintf(stdout, "spin: preprocessing failed %s\n", cmd);
		alldone(1); /* no return, error exit */
	}
	if (a_tmp) (void) unlink((const char *) a);
}

#define OPT_KEY_RUN 1
#define OPT_KEY_PRETTY_PRINT 2
#define OPT_KEY_LTL 3
#define OPT_KEY_LINK 4
#define OPT_KEY_REPLAY 5
#define OPT_KEY_SIMULATE 6
#define OPT_KEY_SEARCH 7
#define OPT_KEY_S1 8
#define OPT_KEY_S2 9

// The format for each `argp_option` struct is as follows:
// 1. The name of the option's long option
// 2. The option's key when passed into the parser, or the short option
// 3. The name printed for the argument, for cases such as -output <FILE>
// 4. Flags for the argument
// 5. A documentation string for the option
static struct argp_option options[] = {
  {0, 'A', 0, 0, "apply slicing algorithm"},
  {0, 'a', 0, 0, "generate a verifier in pan.c"},
  {0, 'B', 0, 0, "no final state details in simulations"},
  {0, 'b', 0, 0, "don't execute printfs in simulation"},
  {0, 'C', 0, 0, "print channel access info (combine with -g etc."},
	{0, 'c', 0, 0, "columnated -s -r simulation output"},
	{0, 'd', 0, 0, "produce symbol-table information"},
	{0, 'D', "yyy", 0, "pass -Dyyy to the preprocessor"},
	{0, 'E', "yyy", 0, "pass yyy to the preprocessor"},
	{0, 'e', 0, 0, "compute synchronous product of multiple never claims (modified by -L)"},
	{0, 'f', 0, 0, "\"..formula..\"  translate LTL "},

  {0, 0, 0, OPTION_DOC, "Into never claim:"},
	{0, 'F', 0, 0, "file  like -f, but with the LTL formula stored in a 1-line file"},
	{0, 'g', 0, 0, "print all global variables"},
	{0, 'h', 0, 0, "at end of run, print value of seed for random nr generator used"},
	{0, 'i', 0, 0, "interactive (random simulation)"},
	{0, 'I', 0, 0, "show result of inlining and preprocessing"},
	{0, 'J', 0, 0, "reverse eval order of nested unlesses"},
	{0, 'j', "N", 0, "skip the first N steps "},

  {0, 0, 0, OPTION_DOC, "In simulation trail:"},
	{0, 'k', 0, 0, "fname use the trailfile stored in file fname, see also -t"},
	{0, 'L', 0, 0, "when using -e, use strict language intersection"},
	{0, 'l', 0, 0, "print all local variables"},
	{0, 'M', 0, 0, "generate msc-flow in tcl/tk format"},
	{0, 'm', 0, 0, "lose msgs sent to full queues"},
	{0, 'N', 0, 0, "fname use never claim stored in file fname"},
	{0, 'n', "N", 0, "seed for random nr generator"},
	{0, 'O', 0, 0, "use old scope rules (pre 5.3.0)"},
  {0, 'o', "NUM", 0, "\nSet optimization level for the program:\n\
1. Turn off dataflow-optimizations in verifier\n\
2. Don't hide write-only variables in verifier\n\
3. Turn off statement merging in verifier\n\
4. Turn on rendezvous optiomizations in verifier\n\
5. Turn on case caching (reduces size of pan.m, but affects reachability reports)\n\
6. Revert to the old rules for interpreting priority tags (pre version 6.2)\n\
7. Revert to the old rules for semi-colon usage (pre version 6.3)\n"},
	{0, 'P', "xxx", 0, "use xxx for preprocessing"},
	{0, 'p', 0, 0, "print all statements"},
	{"pp", OPT_KEY_PRETTY_PRINT, 0, 0, "pretty-print (reformat) stdin, write stdout"},
	{0, 'q', 0, 0, "suppress io for queue N in printouts"},
	{0, 'r', 0, 0, "print receive events"},

  {"replay", OPT_KEY_REPLAY, 0, 0, "replay an error trail-file found earlier\n\
if the model contains embedded c-code, the ./pan executable is used\n\
otherwise spin itself is used to replay the trailfile\n\
note that pan recognizes different runtime options than spin itself"},

  {"run", OPT_KEY_RUN, 0, 0, "(or -search) generate a verifier, and compile and run it\n\
options before -search are interpreted by spin to parse the input\n\
options following a -search are used to compile and run the verifier pan\n\
valid options that can follow a -search argument are in the following section.\n\
Similarly, a -D... parameter can be specified to modify the compilation\n\
and any valid runtime pan argument can be specified for the verification"},
  {"search", OPT_KEY_SEARCH, 0, OPTION_ALIAS, 0},

  {0, 0, 0, OPTION_DOC, "Following a -search or -run argument:"},
  {"bfs", 0, 0, 0, "perform a breadth-first search"},
  {"bfspar", 0, 0, 0, "perform a parallel breadth-first search"},
  {"dfspar", 0, 0, 0, "perform a parallel depth-first search, same as -DNCORE=4"},
  {"bcs", 0, 0, 0, "use the bounded-context-switching algorithm"},
  {"bitstate", 0, 0, 0, "or -bit, use bitstate storage"},
  {"biterate", 0, "N,M", 0, "use bitstate with iterative search refinement (-w18..-w35)\n\
perform N randomized runs and increment -w every M runs\n\
default value for N is 10, default for M is 1\n\
(use N,N to keep -w fixed for all runs)\n\
(add -w to see which commands will be executed)\n\
(add -W if ./pan exists and need not be recompiled)"},
  {"swarm", 0, "N,M", 0, "like -biterate, but running all iterations in parallel"},
  {"link", 0, 0, 0, "file.c link executable pan to file.c"},
  {"collapse", 0, 0, 0, "use collapse state compression"},
  {"noreduce", 0, 0, 0, "do not use partial order reduction"},
  {"hc", 0, 0, 0, "use hash-compact storage"},
  {"noclaim", 0, 0, 0, "ignore all ltl and never claims"},
  {"p_permute", 0, 0, 0, "use process scheduling order random permutation"},
  {"p_rotateN", 0, 0, 0, "use process scheduling order rotation by N"},
  {"p_reverse", 0, 0, 0, "use process scheduling order reversal"},
  {"rhash", 0, 0, 0, "randomly pick one of the -p_... options"},
  {"ltl", 0, 0, 0, "p	verify the ltl property named p"},
  {"safety", 0, 0, 0, "compile for safety properties only"},
  {"i", 0, 0, 0, "use the dfs iterative shortening algorithm"},
  {"a", 0, 0, 0, "search for acceptance cycles"},
  {"l", 0, 0, 0, "search for non-progress cycles"},

  {"S1", OPT_KEY_S1, 0, 0, "separate pan source for claim and model"},
  {"S2", OPT_KEY_S2, 0, OPTION_ALIAS, 0},
  {0, 's', 0, 0, "print send events"},
  {0, 'T', 0, 0, "do not indent printf output"},
  {0, 't', "[N]", 0, "follow [Nth] simulation trail, see also -k"},
  {0, 'U', "yyy", 0, "pass -Uyyy to the preprocessor"},
  {0, 'u', "N", 0, "stop a simulation run after N steps"},
  {0, 'v', 0, 0, "verbose, more warnings"},
  {0, 'w', 0, 0, "very verbose (when combined with -l or -g)"},
  {0, 'x', 0, 0, "internal - reserved use"},
  {0, 'X', 0, 0, "reserved for use by xspin interface"},
  {0, 'Y', 0, OPTION_ALIAS, 0},
  {0, 'Z', 0, OPTION_ALIAS, 0},
  {0, 'V', 0, 0, "print version number and exit"},

  {0},
};

enum opt_level {
  OPT_LEVEL_DATAFLOW,
  OPT_LEVEL_DEAD_VARIABLE_ELIM,
  OPT_LEVEL_STATEMENT_MERGING,
  OPT_LEVEL_RV_MERGING,
  OPT_LEVEL_CASE_CACHING,
  OPT_OLD_PRIO_RULES,
  OPT_NO_IMPLIES_SEMIS,
};

int
optimizations(int nr)
{
	switch (nr) {
	case '1':
		dataflow = 1 - dataflow; /* dataflow */
		if (verbose&32)
		printf("spin: dataflow optimizations turned %s\n",
			dataflow?"on":"off");
		break;
	case '2':
		/* dead variable elimination */
		deadvar = 1 - deadvar;
		if (verbose&32)
		printf("spin: dead variable elimination turned %s\n",
			deadvar?"on":"off");
		break;
	case '3':
		/* statement merging */
		merger = 1 - merger;
		if (verbose&32)
		printf("spin: statement merging turned %s\n",
			merger?"on":"off");
		break;

	case '4':
		/* rv optimization */
		rvopt = 1 - rvopt;
		if (verbose&32)
		printf("spin: rendezvous optimization turned %s\n",
			rvopt?"on":"off");
		break;
	case '5':
		/* case caching */
		ccache = 1 - ccache;
		if (verbose&32)
		printf("spin: case caching turned %s\n",
			ccache?"on":"off");
		break;
	case '6':
		old_priority_rules = 1;
		if (verbose&32)
		printf("spin: using old priority rules (pre version 6.2)\n");
		return 0; /* no break */
	case '7':
		implied_semis = 0;
		if (verbose&32)
		printf("spin: no implied semi-colons (pre version 6.3)\n");
		return 0; /* no break */
	default:
		printf("spin: bad or missing parameter on -o\n");
		// usage();
		break;
	}
	return 1;
}

static void
add_comptime(char *s)
{	char *tmp;

	if (!s || strstr(pan_comptime, s))
	{	return;
	}

	tmp = (char *) emalloc(strlen(pan_comptime)+strlen(s)+2);
	sprintf(tmp, "%s %s", pan_comptime, s);
	pan_comptime = tmp;
}

static struct {
	char *ifsee, *thendo;
	int keeparg;
} pats[] = {
	{ "-bfspar",	"-DBFS_PAR",	0 },
	{ "-bfs",	"-DBFS",	0 },
	{ "-bcs",	"-DBCS",	0 },
	{ "-bitstate",	"-DBITSTATE",	0 },
	{ "-bit",	"-DBITSTATE",	0 },
	{ "-hc",	"-DHC4",	0 },
	{ "-collapse",	"-DCOLLAPSE",	0 },
	{ "-noclaim",	"-DNOCLAIM",	0 },
	{ "-noreduce",	"-DNOREDUCE",	0 },
	{ "-np",	"-DNP",		0 },
	{ "-permuted",	"-DPERMUTED",	0 },
	{ "-p_permute", "-DPERMUTED",	1 },
	{ "-p_rotate",	"-DPERMUTED",	1 },
	{ "-p_reverse",	"-DPERMUTED",	1 },
	{ "-rhash",	"-DPERMUTED",	1 },
	{ "-safety",	"-DSAFETY",	0 },
	{ "-i",		"-DREACH",	1 },
	{ "-l",		"-DNP",		1 },
	{ 0, 0 }
};

static void
set_itsr_n(char *s)	/* e.g., -swarm12,3 */
{	char *tmp;

	if ((tmp = strchr(s, ',')) != NULL)
	{	tmp++;
		if (*tmp != '\0' && isdigit((int) *tmp))
		{	itsr_n = atoi(tmp);
			if (itsr_n < 2)
			{	itsr_n = 0;
	}	}	}
}

static void
add_runtime(char *s)
{	char *tmp;
	int i;

	if (strncmp(s, "-biterate", strlen("-biterate")) == 0)
	{	itsr = 10;	/* default nr of sequential iterations */
		sw_or_bt = 1;
		if (isdigit((int) s[9]))
		{	itsr = atoi(&s[9]);
			if (itsr < 1)
			{	itsr = 1;
			}
			set_itsr_n(s);
		}
		return;
	}
	if (strncmp(s, "-swarm", strlen("-swarm")) == 0)
	{	itsr = -10;	/* parallel iterations */
		sw_or_bt = 1;
		if (isdigit((int) s[6]))
		{	itsr = atoi(&s[6]);
			if (itsr < 1)
			{	itsr = 1;
			}
			itsr = -itsr;
			set_itsr_n(s);
		}
		return;
	}

	for (i = 0; pats[i].ifsee; i++)
	{	if (strncmp(s, pats[i].ifsee, strlen(pats[i].ifsee)) == 0)
		{	add_comptime(pats[i].thendo);
			if (pats[i].keeparg)
			{	break;
			}
			return;
	}	}
	if (strncmp(s, "-dfspar", strlen("-dfspar")) == 0)
	{	add_comptime("-DNCORE=4");
		return;
	}

	tmp = (char *) emalloc(strlen(pan_runtime)+strlen(s)+2);
	sprintf(tmp, "%s %s", pan_runtime, s);
	pan_runtime = tmp;
}

#ifdef __MINGW32__
	/* mingw on PCs doesn't have a definition of getline
	 * so we fall back on using a fixed size buffer, to
	 * avoid having to reimplement getline here·..
	 */
ssize_t
getline(char **lineptr, size_t *n, FILE *stream)
{	static char buffer[8192];

	*lineptr = (char *) &buffer;

	if (!fgets(buffer, sizeof(buffer), stream))
	{	return 0;
	}
	return 1;
}
#endif


struct cli_args {
  int T;
  int usedopts;
  int parse_run; // Set when parsing the options to -run
};

static char* prepend_arg(const char c, const char* arg) {
  char* tmp = emalloc(strlen(arg) + 2 + 1);
  sprintf(tmp, "-%c%s", c, arg);
  return tmp;
}

static error_t parse_opt(int key, char *arg, struct argp_state *state) {
  struct cli_args *args = state->input;

  // Handle the run args separately
  if (args->parse_run) {
    switch (key) {
      case 'D': /* eg -DNP */
      /*	  case 'E': conflicts with runtime arg */
      case 'O': /* eg -O2 */
      case 'U': /* to undefine a macro */
        add_comptime(prepend_arg(key, arg)); break;
#if 0
      case 'w': /* conflicts with bitstate runtime arg */
      verbose += 64; 
      break;
#endif
      case 'W': norecompile = 1; break;
      case OPT_KEY_LTL: add_runtime("-N"); add_runtime("-ltl"); break; /* prop name */
      case OPT_KEY_LINK: add_comptime("-link");
      default: add_runtime(prepend_arg(key, arg)); break; /* -bfs etc. */
    }

    return 0;
  }

  switch (key) {
		case 'A': export_ast = 1; break;
		case 'a': analyze = 1; break;
		case 'B': no_wrapup = 1; break;
		case 'b': no_print = 1; break;
		case 'C': Caccess = 1; break;
		case 'c': columns = 1; break;
    case 'D':
    case 'U': pre_arg_append(prepend_arg(key, arg)); break;
    case 'E': pre_arg_append(arg); break;
    case 'd': dumptab = 1; break;
    case 'e': product++; break; /* see also 'L' */
    case 'F': {
      ltl_file = &state->argv[state->next];
      state->next = state->argc;
      break;
    }
		case 'f': {
      add_ltl = &state->argv[state->next];
      state->next = state->argc;
      break;
    }
    case 'g': verbose +=  1; break;
    case 'h': seedy = 1; break;
    case 'i': interactive = 1; break;
    case 'I': inlineonly = 1; break;
    case 'J': like_java = 1; break;
    case 'j': jumpsteps = atoi(arg); break;
    case 'k': {
      s_trail = 1;
      trailfilename = &state->argv[state->next];
      state->next = state->argc;
      break;
    }
    case 'L': Strict++; break; /* modified -e */
    case 'l': verbose += 2; break;
    case 'M': columns = 2; break;
    case 'm': m_loss = 1; break;
    case 'N': {
      nvr_file = &state->argv[state->next];
      state->next = state->argc;
      break;
    }
    case 'n': args->T = atoi(arg); tl_terse = 1; break;
    case 'O': old_scope_rules = 1; break;
    case 'o': args->usedopts += optimizations(atoi(arg)); break;
    case 'P': {
      assert(strlen(arg) < sizeof(PreProc));
      strcpy(PreProc, arg);
      break;
    }
    case 'p': verbose += 4; break;
    case OPT_KEY_PRETTY_PRINT: pretty_print(); break;
    case 'q': {
      if (isdigit(arg[0])) {
        qhide(atoi(arg));
      }
      break;
    }
    case OPT_KEY_SEARCH:
    case OPT_KEY_REPLAY:
    case OPT_KEY_RUN: {
      switch (key) {
        case OPT_KEY_RUN: {
          Srand((unsigned int) args->T);
        }
        case OPT_KEY_REPLAY: {
          replay = 1;
          add_runtime("-r");
        }
      }

      if (buzzed != 0) {
        argp_failure(state, 1, 0, "cannot combine -x with -run -replay or -search");
        return EINVAL;
      }

      buzzed = 2;
      analyze = 1;

      // Handle future args as passed into the run command
      args->parse_run = 1;
      break;
    }
    case 'r': verbose += 8; break;
    case OPT_KEY_S1:
    case OPT_KEY_S2: separate = atoi(arg); analyze = 1; break; /* S1 or S2 */
    case OPT_KEY_SIMULATE: break; // ignore
    case 's': verbose += 16; break;
    case 'T': notabs = 1; break;
    case 't': {
      s_trail = 1;
      if (isdigit(arg[0])) {
        ntrail = atoi(arg);
      }
      break;
    }
    case 'u': cutoff = atoi(arg); break;
    case 'v': verbose += 32; break;
    case 'V': printf("%s\n", SpinVersion); alldone(0); break;
    case 'w': verbose += 64; break;
    case 'W': norecompile = 1; break; /* 6.4.7: for swarm/biterate */
    case 'x': { /* internal - reserved use */
      if (buzzed != 0) {
        argp_failure(state, 1, 0, "cannot combine -x with -run -search or -replay");
        return EINVAL;
      }
      buzzed = 1; /* implies also -a -o3 */
      pan_runtime = "-d";
      analyze = 1;
      args->usedopts += optimizations('3');
      break;
    }
    case 'X': {
      xspin = notabs = 1;
#ifndef PC
    signal(SIGPIPE, alldone); /* not posix */
#endif
      break;
    }
    case 'Y': limited_vis = 1; break; /* used by xspin */
    case 'Z': preprocessonly = 1; break; /* used by xspin */
    default:
      return ARGP_ERR_UNKNOWN;
  }

  return 0;
}

static struct argp argp = { 
  .options = options, 
  .parser = parse_opt,
  .args_doc = args_doc, 
  .doc = doc,
};

int
main(int argc, char *argv[])
{	Symbol *s;
	int T = (int) time((time_t *)0);
	int usedopts = 0;

	yyin  = stdin;
	yyout = stdout;
	tl_out = stdout;
	strcpy(CurScope, "_");

	assert(strlen(CPP) < sizeof(PreProc));
	strcpy(PreProc, CPP);

  struct cli_args arguments = { 0 };

  argp_parse(&argp, argc, argv, ARGP_LONG_ONLY, 0, &arguments);

	if (columns == 2 && !cutoff)
	{	cutoff = 1024;
	}

	if (usedopts && !analyze)
		printf("spin: warning -o[1..5] option ignored in simulations\n");

	if (ltl_file)
	{	add_ltl = ltl_file-2; add_ltl[1][1] = 'f';
		if (!(tl_out = fopen(*ltl_file, "r")))
		{	printf("spin: cannot open %s\n", *ltl_file);
			alldone(1);
		}
		size_t linebuffsize = 0;
		ssize_t length = getline(&formula, &linebuffsize, tl_out);
		if (!formula || !length)
		{	printf("spin: cannot read %s\n", *ltl_file);
		}
		fclose(tl_out);
		tl_out = stdout;
		*ltl_file = formula;
	}
	if (argc > 1)
	{	FILE *fd = stdout;
		char cmd[512], out2[512];

		/* must remain in current dir */
		strcpy(out1, "pan.pre");

		if (add_ltl || nvr_file)
		{	assert(strlen(argv[1])+6 < sizeof(out2));
			sprintf(out2, "%s.nvr", argv[1]);
			if ((fd = fopen(out2, MFLAGS)) == NULL)
			{	printf("spin: cannot create tmp file %s\n",
					out2);
				alldone(1);
			}
			fprintf(fd, "#include \"%s\"\n", argv[1]);
		}

		if (add_ltl)
		{	tl_out = fd;
			nr_errs = tl_main(2, add_ltl);
			fclose(fd);
			preprocess(out2, out1, 1);
		} else if (nvr_file)
		{	fprintf(fd, "#include \"%s\"\n", *nvr_file);
			fclose(fd);
			preprocess(out2, out1, 1);
		} else
		{	preprocess(argv[1], out1, 0);
		}

		if (preprocessonly)
		{	alldone(0);
		}

		if (!(yyin = fopen(out1, "r")))
		{	printf("spin: cannot open %s\n", out1);
			alldone(1);
		}

		assert(strlen(argv[1])+1 < sizeof(cmd));

		if (strncmp(argv[1], "progress", (size_t) 8) == 0
		||  strncmp(argv[1], "accept", (size_t) 6) == 0)
		{	sprintf(cmd, "_%s", argv[1]);
		} else
		{	strcpy(cmd, argv[1]);
		}
		oFname = Fname = lookup(cmd);
		if (oFname->name[0] == '\"')
		{	int i = (int) strlen(oFname->name);
			oFname->name[i-1] = '\0';
			oFname = lookup(&oFname->name[1]);
		}
	} else
	{	oFname = Fname = lookup("<stdin>");
		if (add_ltl)
		{	if (argc > 0)
				exit(tl_main(2, add_ltl));
			printf("spin: missing argument to -f\n");
			alldone(1);
		}
		printf("%s\n", SpinVersion);
		fprintf(stderr, "spin: error, no filename specified\n");
		fflush(stdout);
		alldone(1);
	}
	if (columns == 2)
	{	if (xspin || (verbose & (1|4|8|16|32)))
		{	printf("spin: -c precludes all flags except -t\n");
			alldone(1);
		}
		putprelude();
	}
	if (columns && !(verbose&8) && !(verbose&16))
	{	verbose += (8+16);
	}
	if (columns == 2 && limited_vis)
	{	verbose += (1+4);
	}

	Srand((unsigned int) T);	/* defined in run.c */
	SeedUsed = T;
	s = lookup("_");	s->type = PREDEF; /* write-only global var */
	s = lookup("_p");	s->type = PREDEF;
	s = lookup("_pid");	s->type = PREDEF;
	s = lookup("_last");	s->type = PREDEF;
	s = lookup("_nr_pr");	s->type = PREDEF; /* new 3.3.10 */
	s = lookup("_priority"); s->type = PREDEF; /* new 6.2.0 */

	yyparse();
	fclose(yyin);

	if (ltl_claims)
	{	Symbol *r;
		fclose(fd_ltl);
		if (!(yyin = fopen(ltl_claims, "r")))
		{	fatal("cannot open %s", ltl_claims);
		}
		r = oFname;
		oFname = Fname = lookup(ltl_claims);
		lineno = 0;
		yyparse();
		fclose(yyin);
		oFname = Fname = r;
		if (0)
		{	(void) unlink(ltl_claims);
	}	}

	loose_ends();

	if (inlineonly)
	{	repro_src();
		return 0;
	}

	chanaccess();
	if (!Caccess)
	{	if (has_provided && merger)
		{	merger = 0;	/* cannot use statement merging in this case */
		}
		if (!s_trail && (dataflow || merger) && (!replay || has_code))
		{	ana_src(dataflow, merger);
		}
		sched();
		alldone(nr_errs);
	}

	return 0;
}

void
ltl_list(char *nm, char *fm)
{
	if (s_trail
	||  analyze
	||  dumptab)	/* when generating pan.c or replaying a trace */
	{	if (!ltl_claims)
		{	ltl_claims = "_spin_nvr.tmp";
			if ((fd_ltl = fopen(ltl_claims, MFLAGS)) == NULL)
			{	fatal("cannot open tmp file %s", ltl_claims);
			}
			tl_out = fd_ltl;
		}
		add_ltl = (char **) emalloc(5 * sizeof(char *));
		add_ltl[1] = "-c";
		add_ltl[2] = nm;
		add_ltl[3] = "-f";
		add_ltl[4] = (char *) emalloc(strlen(fm)+4);
		strcpy(add_ltl[4], "!(");
		strcat(add_ltl[4], fm);
		strcat(add_ltl[4], ")");
		/* add_ltl[4] = fm; */
		nr_errs += tl_main(4, add_ltl);

		fflush(tl_out);
		/* should read this file after the main file is read */
	}
}

void
non_fatal(char *s1, char *s2)
{	extern int yychar; extern char yytext[];

	printf("spin: %s:%d, Error: ",
		Fname?Fname->name:(oFname?oFname->name:"nofilename"), lineno);
#if 1
	printf(s1, s2); /* avoids a gcc warning */
#else
	if (s2)
		printf(s1, s2);
	else
		printf(s1);
#endif
	if (yychar > 0)
	{	if (yychar == SEMI)
		{	printf(" statement separator");
		} else
		{	printf("	saw '");
			explain(yychar);
			printf("'");
	}	}
	if (strlen(yytext)>1)
		printf(" near '%s'", yytext);
	printf("\n");
	nr_errs++;
}

void
fatal(char *s1, char *s2)
{
	non_fatal(s1, s2);
	(void) unlink("pan.b");
	(void) unlink("pan.c");
	(void) unlink("pan.h");
	(void) unlink("pan.m");
	(void) unlink("pan.t");
	(void) unlink("pan.p");
	(void) unlink("pan.pre");
	if (!(verbose&32))
	{	(void) unlink("_spin_nvr.tmp");
	}
	alldone(1);
}

char *
emalloc(size_t n)
{	char *tmp;
	static unsigned long cnt = 0;

	if (n == 0)
		return NULL;	/* robert shelton 10/20/06 */

	if (!(tmp = (char *) malloc(n)))
	{	printf("spin: allocated %ld Gb, wanted %d bytes more\n",
			cnt/(1024*1024*1024), (int) n);
		fatal("not enough memory", (char *)0);
	}
	cnt += (unsigned long) n;
	memset(tmp, 0, n);
	return tmp;
}

void
trapwonly(Lextok *n /* , char *unused */)
{	short i;

	if (!n)
	{	fatal("unexpected error,", (char *) 0);
	}

	i = (n->sym)?n->sym->type:0;

	/* printf("%s	realread %d type %d\n", n->sym?n->sym->name:"--", realread, i); */

	if (realread
	&& (i == MTYPE
	||  i == BIT
	||  i == BYTE
	||  i == SHORT
	||  i == INT
	||  i == UNSIGNED))
	{	n->sym->hidden |= 128;	/* var is read at least once */
	}
}

void
setaccess(Symbol *sp, Symbol *what, int cnt, int t)
{	Access *a;

	for (a = sp->access; a; a = a->lnk)
		if (a->who == context
		&&  a->what == what
		&&  a->cnt == cnt
		&&  a->typ == t)
			return;

	a = (Access *) emalloc(sizeof(Access));
	a->who = context;
	a->what = what;
	a->cnt = cnt;
	a->typ = t;
	a->lnk = sp->access;
	sp->access = a;
}

Lextok *
nn(Lextok *s, int t, Lextok *ll, Lextok *rl)
{	Lextok *n = (Lextok *) emalloc(sizeof(Lextok));
	static int warn_nn = 0;

	n->uiid = is_inline();	/* record origin of the statement */
	n->ntyp = (unsigned short) t;
	if (s && s->fn)
	{	n->ln = s->ln;
		n->fn = s->fn;
	} else if (rl && rl->fn)
	{	n->ln = rl->ln;
		n->fn = rl->fn;
	} else if (ll && ll->fn)
	{	n->ln = ll->ln;
		n->fn = ll->fn;
	} else
	{	n->ln = lineno;
		n->fn = Fname;
	}
	if (s) n->sym  = s->sym;
	n->lft  = ll;
	n->rgt  = rl;
	n->indstep = DstepStart;

	if (t == TIMEOUT) Etimeouts++;

	if (!context) return n;

	if (t == 'r' || t == 's')
		setaccess(n->sym, ZS, 0, t);
	if (t == 'R')
		setaccess(n->sym, ZS, 0, 'P');

	if (context->name == claimproc)
	{	int forbidden = separate;
		switch (t) {
		case ASGN:
			printf("spin: Warning, never claim has side-effect\n");
			break;
		case 'r': case 's':
			non_fatal("never claim contains i/o stmnts",(char *)0);
			break;
		case TIMEOUT:
			/* never claim polls timeout */
			if (Ntimeouts && Etimeouts)
				forbidden = 0;
			Ntimeouts++; Etimeouts--;
			break;
		case LEN: case EMPTY: case FULL:
		case 'R': case NFULL: case NEMPTY:
			/* status becomes non-exclusive */
			if (n->sym && !(n->sym->xu&XX))
			{	n->sym->xu |= XX;
				if (separate == 2) {
				printf("spin: warning, make sure that the S1 model\n");
				printf("      also polls channel '%s' in its claim\n",
				n->sym->name); 
			}	}
			forbidden = 0;
			break;
		case 'c':
			AST_track(n, 0);	/* register as a slice criterion */
			/* fall thru */
		default:
			forbidden = 0;
			break;
		}
		if (forbidden)
		{	printf("spin: never, saw "); explain(t); printf("\n");
			fatal("incompatible with separate compilation",(char *)0);
		}
	} else if ((t == ENABLED || t == PC_VAL) && !(warn_nn&t))
	{	printf("spin: Warning, using %s outside never claim\n",
			(t == ENABLED)?"enabled()":"pc_value()");
		warn_nn |= t;
	} else if (t == NONPROGRESS)
	{	fatal("spin: Error, using np_ outside never claim\n", (char *)0);
	}
	return n;
}

Lextok *
rem_lab(Symbol *a, Lextok *b, Symbol *c)	/* proctype name, pid, label name */
{	Lextok *tmp1, *tmp2, *tmp3;

	has_remote++;
	c->type = LABEL;	/* refered to in global context here */
	fix_dest(c, a);		/* in case target of rem_lab is jump */
	tmp1 = nn(ZN, '?',   b, ZN); tmp1->sym = a;
	tmp1 = nn(ZN, 'p', tmp1, ZN);
	tmp1->sym = lookup("_p");
	tmp2 = nn(ZN, NAME,  ZN, ZN); tmp2->sym = a;
	tmp3 = nn(ZN, 'q', tmp2, ZN); tmp3->sym = c;
	return nn(ZN, EQ, tmp1, tmp3);
#if 0
	      .---------------EQ-------.
	     /                          \
	   'p' -sym-> _p               'q' -sym-> c (label name)
	   /                           /
	 '?' -sym-> a (proctype)     NAME -sym-> a (proctype name)
	 / 
	b (pid expr)
#endif
}

Lextok *
rem_var(Symbol *a, Lextok *b, Symbol *c, Lextok *ndx)
{	Lextok *tmp1;

	has_remote++;
	has_remvar++;
	dataflow = 0;	/* turn off dead variable resets 4.2.5 */
	merger   = 0;	/* turn off statement merging for locals 6.4.9 */
	tmp1 = nn(ZN, '?', b, ZN); tmp1->sym = a;
	tmp1 = nn(ZN, 'p', tmp1, ndx);
	tmp1->sym = c;
	return tmp1;
#if 0
	cannot refer to struct elements
	only to scalars and arrays

	    'p' -sym-> c (variable name)
	    / \______  possible arrayindex on c
	   /
	 '?' -sym-> a (proctype)
	 / 
	b (pid expr)
#endif
}

void
explain(int n)
{	FILE *fd = stdout;
	switch (n) {
	default:	if (n > 0 && n < 256)
				fprintf(fd, "'%c' = ", n);
			fprintf(fd, "%d", n);
			break;
	case '\b':	fprintf(fd, "\\b"); break;
	case '\t':	fprintf(fd, "\\t"); break;
	case '\f':	fprintf(fd, "\\f"); break;
	case '\n':	fprintf(fd, "\\n"); break;
	case '\r':	fprintf(fd, "\\r"); break;
	case 'c':	fprintf(fd, "condition"); break;
	case 's':	fprintf(fd, "send"); break;
	case 'r':	fprintf(fd, "recv"); break;
	case 'R':	fprintf(fd, "recv poll %s", Operator); break;
	case '@':	fprintf(fd, "@"); break;
	case '?':	fprintf(fd, "(x->y:z)"); break;
#if 1
	case NEXT:	fprintf(fd, "X"); break;
	case ALWAYS:	fprintf(fd, "[]"); break;
	case EVENTUALLY: fprintf(fd, "<>"); break;
	case IMPLIES:	fprintf(fd, "->"); break;
	case EQUIV:	fprintf(fd, "<->"); break;
	case UNTIL:	fprintf(fd, "U"); break;
	case WEAK_UNTIL: fprintf(fd, "W"); break;
	case IN: fprintf(fd, "%sin", Keyword); break;
#endif
	case ACTIVE:	fprintf(fd, "%sactive",	Keyword); break;
	case AND:	fprintf(fd, "%s&&",	Operator); break;
	case ASGN:	fprintf(fd, "%s=",	Operator); break;
	case ASSERT:	fprintf(fd, "%sassert",	Function); break;
	case ATOMIC:	fprintf(fd, "%satomic",	Keyword); break;
	case BREAK:	fprintf(fd, "%sbreak",	Keyword); break;
	case C_CODE:	fprintf(fd, "%sc_code",	Keyword); break;
	case C_DECL:	fprintf(fd, "%sc_decl",	Keyword); break;
	case C_EXPR:	fprintf(fd, "%sc_expr",	Keyword); break;
	case C_STATE:	fprintf(fd, "%sc_state",Keyword); break;
	case C_TRACK:	fprintf(fd, "%sc_track",Keyword); break;
	case CLAIM:	fprintf(fd, "%snever",	Keyword); break;
	case CONST:	fprintf(fd, "a constant"); break;
	case DECR:	fprintf(fd, "%s--",	Operator); break;
	case D_STEP:	fprintf(fd, "%sd_step",	Keyword); break;
	case D_PROCTYPE: fprintf(fd, "%sd_proctype", Keyword); break;
	case DO:	fprintf(fd, "%sdo",	Keyword); break;
	case DOT:	fprintf(fd, "."); break;
	case ELSE:	fprintf(fd, "%selse",	Keyword); break;
	case EMPTY:	fprintf(fd, "%sempty",	Function); break;
	case ENABLED:	fprintf(fd, "%senabled",Function); break;
	case EQ:	fprintf(fd, "%s==",	Operator); break;
	case EVAL:	fprintf(fd, "%seval",	Function); break;
	case FI:	fprintf(fd, "%sfi",	Keyword); break;
	case FULL:	fprintf(fd, "%sfull",	Function); break;
	case GE:	fprintf(fd, "%s>=",	Operator); break;
	case GET_P:	fprintf(fd, "%sget_priority",Function); break;
	case GOTO:	fprintf(fd, "%sgoto",	Keyword); break;
	case GT:	fprintf(fd, "%s>",	Operator); break;
	case HIDDEN:	fprintf(fd, "%shidden",	Keyword); break;
	case IF:	fprintf(fd, "%sif",	Keyword); break;
	case INCR:	fprintf(fd, "%s++",	Operator); break;
	case INAME:	fprintf(fd, "inline name"); break;
	case INLINE:	fprintf(fd, "%sinline",	Keyword); break;
	case INIT:	fprintf(fd, "%sinit",	Keyword); break;
	case ISLOCAL:	fprintf(fd, "%slocal",  Keyword); break;
	case LABEL:	fprintf(fd, "a label-name"); break;
	case LE:	fprintf(fd, "%s<=",	Operator); break;
	case LEN:	fprintf(fd, "%slen",	Function); break;
	case LSHIFT:	fprintf(fd, "%s<<",	Operator); break;
	case LT:	fprintf(fd, "%s<",	Operator); break;
	case MTYPE:	fprintf(fd, "%smtype",	Keyword); break;
	case NAME:	fprintf(fd, "an identifier"); break;
	case NE:	fprintf(fd, "%s!=",	Operator); break;
	case NEG:	fprintf(fd, "%s! (not)",Operator); break;
	case NEMPTY:	fprintf(fd, "%snempty",	Function); break;
	case NFULL:	fprintf(fd, "%snfull",	Function); break;
	case NON_ATOMIC: fprintf(fd, "sub-sequence"); break;
	case NONPROGRESS: fprintf(fd, "%snp_",	Function); break;
	case OD:	fprintf(fd, "%sod",	Keyword); break;
	case OF:	fprintf(fd, "%sof",	Keyword); break;
	case OR:	fprintf(fd, "%s||",	Operator); break;
	case O_SND:	fprintf(fd, "%s!!",	Operator); break;
	case PC_VAL:	fprintf(fd, "%spc_value",Function); break;
	case PNAME:	fprintf(fd, "process name"); break;
	case PRINT:	fprintf(fd, "%sprintf",	Function); break;
	case PRINTM:	fprintf(fd, "%sprintm",	Function); break;
	case PRIORITY:	fprintf(fd, "%spriority", Keyword); break;
	case PROCTYPE:	fprintf(fd, "%sproctype",Keyword); break;
	case PROVIDED:	fprintf(fd, "%sprovided",Keyword); break;
	case RCV:	fprintf(fd, "%s?",	Operator); break;
	case R_RCV:	fprintf(fd, "%s??",	Operator); break;
	case RSHIFT:	fprintf(fd, "%s>>",	Operator); break;
	case RUN:	fprintf(fd, "%srun",	Operator); break;
	case SEP:	fprintf(fd, "token: ::"); break;
	case SEMI:	fprintf(fd, ";"); break;
	case ARROW:	fprintf(fd, "->"); break;
	case SET_P:	fprintf(fd, "%sset_priority",Function); break;
	case SHOW:	fprintf(fd, "%sshow", Keyword); break;
	case SND:	fprintf(fd, "%s!",	Operator); break;
	case STRING:	fprintf(fd, "a string"); break;
	case TRACE:	fprintf(fd, "%strace", Keyword); break;
	case TIMEOUT:	fprintf(fd, "%stimeout",Keyword); break;
	case TYPE:	fprintf(fd, "data typename"); break;
	case TYPEDEF:	fprintf(fd, "%stypedef",Keyword); break;
	case XU:	fprintf(fd, "%sx[rs]",	Keyword); break;
	case UMIN:	fprintf(fd, "%s- (unary minus)", Operator); break;
	case UNAME:	fprintf(fd, "a typename"); break;
	case UNLESS:	fprintf(fd, "%sunless",	Keyword); break;
	}
}
