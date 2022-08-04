# SPIN - Verification Software - Version 6.5 - July 2019
#
# This file is part of the public release of Spin. It is subject to the
# terms in the LICENSE file that is included in this source directory.
# Tool documentation is available at http://spinroot.com

CC?=gcc
CFLAGS?=-O2 -DNXT -Wall -pedantic
	# on some systems add: -I/usr/include
	# on a PC:    make CFLAGS="-O2 -DNXT -DPC"
	# on Solaris: make CFLAGS="-O2 -DNXT -DSOLARIS"
	# on a Mac:   make CFLAGS="-O2 -DNXT -DMAC"
	# on HP-UX:   make CFLAGS="-O2 -DNXT -Aa"
	# debugging:  make CFLAGS="-pg -g -DNXT"
	# or:         make CC=clang CFLAGS="-fsanitize=address -g"

# for a more picky compilation use gcc-4 and add:
PICKY=-std=c99 -Wstrict-prototypes -pedantic -fno-strength-reduce \
	-fno-builtin -W -Wshadow -Wpointer-arith \
	-Wcast-qual -Winline -Wall

# when running spin with a different compiler:
			# on OS2:         spin -Picc -E/Pd+ -E/Q+
			# for Visual C++: spin -PCL  -E/E

YACC?=yacc		# on Solaris: /usr/ccs/bin/yacc
YFLAGS=-v -d 		# creates y.output and y.tab.h
DESTDIR?=/usr/local
INSTALL?=cp		# on linux: install -D

SRCS = spinlex.c sym.c vars.c main.c msc_tcl.c \
	mesg.c flow.c sched.c run.c pangen1.c pangen2.c \
	pangen3.c pangen4.c pangen5.c guided.c dstep.c \
	structs.c pangen6.c pangen7.c reprosrc.c \
	tl_parse.c tl_lex.c tl_main.c tl_trans.c \
	tl_buchi.c tl_mem.c tl_rewrt.c tl_cache.c

OBJS = $(patsubst %, %.o, $(SRCS))
DEPS = $(patsubst %, %.d, $(SRCS))

spin: makefile spin.o $(OBJS)
	$(CC) $(CFLAGS) -o spin spin.o $(OBJS) $(LDFLAGS)

install: spin
	$(INSTALL) spin $(DESTDIR)/bin/spin
	$(INSTALL) ../Man/spin.1 $(DESTDIR)/share/man/man1/spin.1

spin.o:	makefile spin.y
	$(YACC) $(YFLAGS) spin.y
	$(CC) $(CFLAGS) $(CPPFLAGS) -c y?tab.c
	rm -f y?tab.c
	mv y?tab.o spin.o

%.c.o: %.c
	$(CC) $(CFLAGS) -o $@ -c $< -MMD

clean:
	rm -f spin *.o *.d y?tab.[ch] y.output y.debug
	rm -f pan.[chmotb] a.out core *stackdump

.PHONY: clean install
