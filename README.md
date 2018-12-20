# Spin
## An Efficient Logic Model Checker for the Verification of Multi-threaded Code

Spin is an open-source software verification tool that was originally
developed (starting in 1980) in the Computing Science Research Center of Bell Labs
(the Unix group). It is often considered the most widely used formal verification tool.

Compilation and installation is trivial (see the makefile) and the only dependencies
are the use of a C compiler, yacc or byacc, and a small number of standard
unix/linux/cygwin-like tools (like make, mv, and rm). With help of a related tool
[Modex](http://spinroot.com/modex) Spin can verify C code directly, but the most
common use of the tool is to write a formal specification of the essence of an
application to be verified in a C-like meta-language called ProMeLa (Process Meta
Language). Annual Symposia and Workshops on the tool have been held since 1995.

The main site for access to manuals, tutorials, and papers explaining the theory
behind the tool is [http://spinroot.com](http://spinroot.com).

This repository contains the most recent version of the sources. Updates that are more
recent than the version.h files were made after the most recent release. When a new
release is issued, the version.h file is also updated.

The tool supports a range of different verification algorithms, including depth-first,
breadth-first, parallel/multi-core, bounded depth, bitstate search (using Bloom filter
theory), partial order reduced, and swarm search (using arbitrarily many cpus).

