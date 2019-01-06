Contents
--------
The files in this set contain the text of examples
used in the 1991 Design and Validation of Computer
Protocols book.  The name of each file corresponds to the
page number in the book where the example appears in its
most useful version.  The overview below gives a short
descriptive phrase for each file.

Description       Page Nr = Filename prefix
-----------       -------------------------
hello world       p95.1
tiny examples     p94 p95.2 p96.1 p97.1 p97.2 p101 p102 p104.1
useful demos      p99 p104.2 p105.2 p116 p248
mutual exclusion  p96.2 p105.1 p117 p320
Lynch's protocol  p107 p312
alternatin bit    p123
chappe's protocol p319

We have renamed the main promela files with the standard file
extension .pml, and gave all promela files that are not meant to be
used standalone, but only as include files, the extension .h.
This gives 28 files with extension .pml, and 17 more with extensions .h.
We've also renamed variables named 'in' in the original version of
each file with 'inp' or 'cnt', to avoid the name-clash with what is
today a keyword, starting with Spin version 6.0.
Other minor changes include moving channel declarations to the start
of a proctype declaration, to satisfy new syntax rules, etc.

Large runs
----------
ackerman's fct    p108	# read info at start of the file

Pftp Protocol
-------------
upper tester      p325.test	# not runnable
flow control l.   p329 p330
session layer     p337.pftp.ses p342.pftp.ses1 p347.pftp.ses5
all pftp          App.F.pftp - plus 8 include files

See also the single file version of pftp in: Test/pftp.pml

General
-------
Use these examples for inspiration, and to get 
acquainted with the language and the Spin software.

All examples - except p123.pml - can be used with both version
1 and version 2 of SPIN. (p123.pml was modifed for version 2.0
to use the new syntax for remote referencing).

If you repeat the runs that are listed in the book for
these examples, you should not expect to get the same
numbers in the result - given the algorithmic improvements 
that have been made since book version of Spin Version 1.0.
Generally, the numbers of states, memory, and runtime should
all be lower (sometimes considerably so) than what the first
book reported.

For instance, for p329.pml, the book (Spin V1.0) says
on pg. 332, using a BITSTATE run, that there are:
	90845 + 317134 + 182425 states (stored + linked + matched)
Spin V6.0 (December 2010) reports lower numbers:
	56713 +  35321 +  76958 states (stored + atomic + matched)

If you repeat a BITSTATE run, of course, by the nature of the
machine dependent effect of hashing, you may get different
coverage and hash-factors for larger runs.  The implementation
of the hash functions has also been changed to improve their
performance and quality, so the numbers you see will likely differ.

The last set of files (prefixed App.F) is included for completeness.
As explained in the book: don't expect to be able to do an
exhaustive verification for this specification as listed.
In chapter 14 it is illustrated how the spec can be broken up
into smaller portions that are more easily verified.

Some Small Experiments
-----------------------
Try:
	spin p95.1.pml     # small simulation run

	spin -s p108.pml   # a bigger simulation run, track send stmnts
	spin -c p108.pml   # same with different output format

	spin -a p312.pml   # lynch's protocol - generate verifier
	cc -o pan pan.c    # compile it for exhaustive verification
	./pan              # prove correctness of assertions etc.
	spin -t -r -s p312.pml # display the error trace

you can edit p312.pml to change all three channel declarations in init
to look like:	``chan AtoB = [1] of { mtype byte }''
and repeat the last four steps for a more legible error trace.

	spin -a p123.pml   # alternating bit protocol - generate verifier
	cc -o pan pan.c    # compile it for exhaustive verification
	pan -a             # check violations of the never claim
	spin -t -r -s p123.pml # display the error trace

for an alternative view of these runs try the new graphical
interface ispin (the successor to xspin), and repeat the experiments.

============================================
Updated for Spin Version 6, December 3, 2010

