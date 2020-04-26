# Overview
These are some generic guidelines for downloading and installing Spin and related software on Unix/Linux and Windows systems. Refer to [http://spinroot.com/spin/whatispin.html] for a general description of Spin, with pointers to more detailed(manual pages, tutorials, introductory papers, books, etc.
Spin is distributed freely in source form to encourage research in formal verification, and to help a support friendly and open exchange of algorithms, ideas, and tools.

#### License
The original version of the Spin source code was developed by Gerard Holzmann at Bell Laboratories between 1980 and 1990. It was first publically released in January 1991, initially through the Netlib source code repository. It has been distributed freely since then for research and educational use, without any guarantee of any kind expressed or implied. 
On 30 December 2015 Alcatel-Lucent (the company that inherited Bell Laboratories from AT&T in the trivestiture from 1996) transfered the copyright to all sources to Gerard Holzmann to support a standard open source release under the BSD 3-Clause license. Starting with Spin Version 6.4.5 all Spin code, sources and executables, are now available under the BSD 3-Clause license.
Spin is also part of the stable release of Debian, and is starting to show up in newer Ubuntu releases (16.10+), so that you'll soon be able to install it with a standard `sudo_ _apt-get install spi` command.
From the early days of the Plan9 Operating System, Spin has also been part of that distribution and older version can be found, for instance, in the Plan9 distribution from UC Berkeley.

### Downloading
Spin runs on any Unix and Linux-like system, and on most flavors of Windows PCs, and on Macs.
Precompiled binary executables for some popular types of machines are available at [http://spinroot.com/spin/Bin/index.html].
The distributed binaries have an extension that matches the Spin version number, such as _spin649.exe_. To install the binary, rename it to plain _spin_ or _spin.exe_ (on PCs) and copy it into your bin directory.
If you have machine type that is not available there, or prefer to compile from source, then follow the more detailed instructions below.
___
## Installing Spin
___

### 2a. Installing Spin on a Unix/Linux System
Clone the [http://github.com/nimble-code/Spin] repository and type: `cd Spin/Src; make`
If you are on a SOLARIS system, edit the makefile and add -DSOLARIS to the compiler directives in the makefile first. Similarly, if you use a different C compiler than defined in the makefile, edit the makefile first. You need to have at least a C compiler (eg gcc) and a copy of yacc.

* If all else fails, you can also compile everything with the following line: `yacc -v -d spin.y; cc -o spin *.c`

Spin should compile without warnings. Install the executable version of spin in a directory that is within your default search path (such as your home bin directory, or /usr/local/bin etc.)

To test the basic sanity of the Spin executable, or to get familiar with the basic usage of Spin, go to the _Examples_ directory, and follow the instructions in README.tests file that can be found there.

#### Adding iSpin (Unix/Linux)
iSpin is an optional, but recommended, graphical user interface to Spin, written in Tcl/Tk. To obtain Tcl/Tk, see under _Related software_ below. The iSpin source can be found the iSpin/ subdirectory.
iSpin is compatible with Tcl/Tk version 8.4 and 8.5.
The tool prints the version numbers of Spin, iSpin, and Tcl/Tk when it starts up. You can also check separately which version of Tcl/Tk you have installed by executing the following commands in `wish` (a Tcl/Tk command shell): 
`info tclversion`
`puts $tk_version`
You can find out which version of Spin you have by typing, at a shell command prompt by typing: `spin -V`

Both Spin and iSpin need a working version of a C compiler installed on your system (by default gcc).
iSpin can also make use the graph layout program `dot` if it is available on your system. For information on dot, see _Related software_.
To install iSpin run the iSpin/install.sh script (after possibly editing it), and invoke the program by typing	`ispin` or `ispin spec.pml`

Check the online Help menus in ispin for more details on routine use.</ul>

### 2b. Installing Spin on a Windows
If you just need to update the Spin executable itself, download a new version from [http://spinroot.com/spin/Bin/index.html] and make sure it's in your search path.
You can find out what your search path is set to by typing `set` at an MS-DOS prompt -- this prints a list of all defined variables in your environment, including the search path that is used to find executable commands. (Note that you may need to set the search path in the environment variables)

If you use Spin from the command line (i.e., without iSpin), be warned that some command shells, e.g., the MKS Korn-shell, have none-standard rules for argument parsing (i.e., you can not reliably quote an argument that contains spaces, such as an LTL formula). In most cases this will not be much of a problem, except with the conversion of LTL formula with the `spin -f` option.
You can avoid problems by always using single-quotes, e.g.: `spin -f '[]<>p'`
You can also circumvent the problem by using inline LTL formula, which are supported in Spin version 6 and later or by using sping option -F instead of -f, to read LTL formula from a file instead of the command line.
To run Spin, also with the precompiled version, you need a working C-compiler and a C-preprocessor, because Spin generates its model checking software as C-source files that require compilation before a verification can be performed. This guarantees fast model checking, because each model checker can be optimized to the specific model being checked. Check, for instance, if you can compile and run a minimal C program succesfully, e.g.:

	#include >stdio.h>
	int main(void) { printf("hello\n"); }

  To find a public version of a C compiler and some instructions on how to
  install it see _Related Software_ below.

#### adding iSpin (PC)
To run iSpin on a PC, you need the PC version of Tcl/Tk (see _Related Software_).
Copy the ispin.tcl file into a directory where you plan to work, or put a shortcut to this file on the Desktop or in the Start Menu. If you keep the extension .tcl, make sure it is recognized as a `wish` file by the system, so that ispin starts when you double click the ispin.tcl script.
On _cygwin_, copy the ispin*.tcl file to /bin/ispin and make it executable. You can then use ispin as a normal Unix-style command, and you can pass the name of a filename to it, for instance as: `ispin leader.pml`

An alternative is to start ispin from its source by invoking wish:
     `wish -f ispin.tcl`
  or
    `wish -f /bin/ispin`
(you have to know where the source is stored for this to work of course).
  
An even more indirect way to force ispin to startup is to first start `wish` from the Windows Start Menu, under Programs, then select the larger window that comes up (the command window), and cd to the directory where you've stored the ispin tcl/tk source file. Then you can then start it up by typing: `source ispin.tcl` and you should be up and running.

The PC installation assumes that you have `gcc` installed. Nothing much in Spin will work without access to a preprocessor, but you can still do a few things (like simulations). The C-compiler (e.g., gcc) is required for all verifications and for the automata views in iSpin. 
If iSpin cannot locate the gcc executable on your system, it will put up a warning message when it first starts up.  On recent versions of cygwin gcc is actually a link from /bin/gcc to /bin/gcc-3 or /bin/gcc-4
Depending on how the name changes, iSpin may not always recognize it. To fix this -- edit the iSpin source (it's tcl/tk text) and define CC as `set CC c:/cygwin/bin/gcc-5` or whatever the new name is.

#### 2c. Installing Spin on a Mac

Compile Spin from its sources, as described under 2a for Unix systems in general, while following the suggestions below, which were provided by Dominik Brettnacher.
If you prefer to use `clang` instead opf `gcc`, you can  try building the Spin executable by calling `make CC=clang`

#### adding iSpin
On the Mac, iSpin was reported to work correctly with Tcl/Tk Aqua, which offers a self-contained binary distribution for the Mac. Use, for instance, "TclTkAquaStandalone", version 8.4.4 or later from [http://www.maths.mq.edu.au/~steffen/tcltk/TclTkAqua/]

Some users reported that on a Mac iSpin by default places its temporary files into the root directory. This is nasty if you have admin privileges and probably leads to error messages if you don't. To prevent  his, add a "cd" statement to iSpin (no arguments, just cd by itself on a line), as the first command executed. Place it, for instance, directly after the opening comments in the file. This makes iSpin use the home directory for these files.
TclTk Aqua also provides the possibility to start a script when being run. For instance, to make iSpin start if you launch the TCL interpreter: move the ispin file into the "Wish Shell.app", as follows:
` chmod -R u+w Wish\ Shell.app`
`mkdir Wish\ Shell.app/Contents/Resources/Scripts`
`mv ispin*.tcl Wish\ Shell.app/Contents/Resources/Scripts/AppMain.tcl`
___

### Related Software
Below are some pointers to public domain versions of related software packages. Some (e.g, a C compiler) are required to run Spin, but most other packages are optional extensions or alternatives.

* GCC (needed for Spin)
  On Unix/Linux you probably have gcc, or an equivalent, installed. On the PC you need either a copy of Visual Studio Express (for the cl command), or an installation of gcc with minimally the executable gcc.exe in your search path, together with all the standard C library routines and header files. You can get good free version of all these files with the cygwin toolkit, which is mostly self-installing and available from: [http://www.cygwin.com/]
  See also what's available at [http://spinroot.com/spin/Bin/index.html].

* Tcl/Tk Wish (needed for iSpin only)
  To run iSpin you'll need Tcl/Tk. Tcl/Tk was written by John Ousterhout (john.ousterhout@eng.sun.com) and is public domain. It can be obtained (for PCs or Unix) from cygwin, or from: [http://www.tcl.tk/] or also (a more recent extension): [http://www.activestate.com/Products/ActiveTcl/]. More details may be found in netnews-group: comp.lang.tcl

* Yacc (optional)
  To compile Spin itself from its sources on a PC, you'll need to have a copy of yacc installed. A public domain version for a Windows PC can most easily be obtained from cygwin, and many other places.
  (You don't need yacc on the PC if you use the pre-compiled version of Spin for the pc in the pc*.zip file from the distribution) Look at the file make_it.bat for an example on how to perform the compilation.
  On a Unix/Linux/Ubuntu system you can install yacc in the usual way, with apt-get.

* Dot (optional)
  Dot is a graph layout tool developed by Stephen North and colleagues at AT&amp;T. iSpin can make use of dot to show a graph layout of the state-machines in the automata-view option (recommended!). To obtain Dot, see [http://www.graphviz.org/]. There are both PC and Unix versions of dot available.
  If you accept the default installation on a PC, you will need to define the location of dot.exe in the ispin source, for instance as follows (or wherver the actual dot.exe is installed):
	`set DOT "C:/Program\\ Files\ATT\Graphviz/bin/dot.exe"`
  (the line that sets the location of DOT appears near the top of the ispin.tcl file).

* Etch (optional)
  Etch, short for Enhanced Type CHecker, can perform more thorough static checking than the  default SPIN type checker, using type inference to reconstruct types of  channels which can only be incompletely specified in Promela. The  techniques are described in [ http://spinroot.com/spin/symposia/ws05/002_paper.pdf].
  The Etch tool can be downloaded from: [http://www.doc.ic.ac.uk/~afd/etch/].

* TopSpin (optional)
  TopSpin is a symmetry reduction package for Spin, developed by Alastair Donaldson. It can be applied to a Promela model and, provided that the model adheres to some restrictions (detailed in a user manual) uses computational group theory to determine a group of component symmetries associated with the model. The tool can modify the model checking algorithm used by Spin to exploit the symmetries during verification, resulting in reduced memory use and in many cases also shorter verification time. The package can be downloaded from: [http://www.doc.ic.ac.uk/~afd/topspin/].

* JSpin (optional)
  jSpin, developed by [http://www.weizmann.ac.il/sci-tea/benari] Moti Ben-Ari, is
an alternative to the iSpin GUI written in Java instead of Tcl/Tk. It is meant as a teaching aid. See:
[http://www.weizmann.ac.il/sci-tea/benari/software-and-learning-materials/jspin/]. The jSpin tool can be configured for use on Linux and Macs, and can also run under Windows, with or without cygwin installed (e.g., with mingw). The jSpin tool can be downloaded from github: [https://github.com/motib">https://github.com/motib]

* Erigone (optional)
  Erigone, also developed by Moti Ben-Ari, is a reimplementation of a subset of an early version of Spin, meant for educational use. Erigone is written in Ada 2005 instead of C.  Erigone can be downloaded from the github link above.

* SpinJa (optional)
  SpinJa is reimplementation of a subset of Spin in Java, developed by Marc de Jonge at Twente University in The Netherlands. A more detailed description of SpinJa was presented at the 2010 Spin Symposium
by Marc de Jonge and Theo Ruys. The tool can be downloaded from: [http://code.google.com/p/spinja/].

* Ltl2Ba (optional)
  A faster method to generate very small never claims from LTL formulae, developed by Denis Oddoux and Paul Gastin is available online in source form: [ http://spinroot.com/spin/Src/ltl2ba.tar.gz]. The latest version can also be obtained from the authors website via: [http://www.lsv.ens-cachan.fr/~gastin/ltl2ba/download.php]
  See also [http://www.lsv.ens-cachan.fr/~gastin/ltl2ba/index.php].
  The C source code can be linked with Spin, or run as a standalone tool.
  For an overview of related conversion tools see: [http://spot.lip6.fr/wiki/LtlTranslationAlgorithms].

* Swarm (optional)
  A front-end to Spin to perform swarm/cloud verifications. See [http://spinroot.com/swarm/].

* Runspin and Parsepan (optional)
  Two useful scripts by Theo Ruys, to help with setting up (and remembering) configurations for multiple verification runs: [http://github.com/tcruys/runspin] and [http://github.com/tcruys/parsepan]

