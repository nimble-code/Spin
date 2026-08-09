# Spin

> **An Efficient Logic Model Checker for the Formal Verification of Multi-threaded Software**

Spin is an open-source software verification tool originally developed starting in 1980 by Gerard J. Holzmann in the Computing Science Research Center of Bell Labs (the Unix group). It is widely considered one of the most powerful and popular formal verification tools available.

---

## 📌 Overview

Spin is designed for formal verification of multi-threaded, concurrent, and distributed software systems. 

Applications are typically specified in a high-level modeling language called **PROMELA** (*Process Meta Language*). Spin can simulate system executions or generate optimized C source code (`pan.c`) that exhaustively verifies the system for properties such as:
- **Deadlocks** (invalid end states)
- **Data Races & Invariant Violations** (assert failures)
- **Unreachable Code**
- **LTL Properties** (Linear Temporal Logic formulas for safety and liveness)

Spin can also be used directly with C source code via the companion tool [Modex](http://spinroot.com/modex).

---

## ✨ Features & Verification Algorithms

Spin supports a broad range of formal verification algorithms and state-space reduction techniques:

- **Depth-First Search (DFS) & Breadth-First Search (BFS)**
- **Partial Order Reduction (POR)** for state space compression
- **Bitstate Search** (using Bloom filter techniques for extremely large state spaces)
- **Multi-Core / Parallel Verification**
- **Bounded-Depth Search**
- **Swarm Search** (randomized parallel search across CPU cores)
- **LTL to Büchi Automata** conversion for temporal logic checks

---

## 🛠️ Build and Installation

### Prerequisites

To compile Spin, you need standard C build tools:
- A **C Compiler** (`gcc` or `clang`)
- **`yacc`** or **`byacc`** (or `bison -y`)
- Standard Unix utilities (`make`, `mv`, `rm`)

### Compilation

Clone the repository and build using `make`:

```bash
git clone https://github.com/nimble-code/Spin.git
cd Spin
make
```

To install the `spin` executable into standard PATH (`/usr/local/bin` by default):

```bash
sudo make install
```

---

## 🚀 Quick Start

### 1. Simulation Mode

You can run a random simulation of a PROMELA model (e.g. from the [`Examples/`](file:///Volumes/External/Code/Spin/Examples) directory):

```bash
spin Examples/hello.pml
```

### 2. Verification Mode

To perform an exhaustive verification of a specification:

```bash
# 1. Generate the verifier source code (pan.c)
spin -a model.pml

# 2. Compile the verifier
gcc -O2 -o pan pan.c

# 3. Run the verifier to search for errors
./pan
```

If an error (e.g. deadlock or assertion failure) is found, a trace file (`model.pml.trail`) is generated. You can replay the error path with:

```bash
spin -t -p model.pml
```

---

## 🖥️ Graphical Interface (iSpin)

Spin includes an optional Tcl/Tk-based GUI named **iSpin**, located in [`optional_gui/ispin.tcl`](file:///Volumes/External/Code/Spin/optional_gui/ispin.tcl).

To run iSpin (requires Tcl/Tk installed):

```bash
wish optional_gui/ispin.tcl
```

---

## 📖 Documentation & Links

- **Official Website**: [http://spinroot.com](http://spinroot.com)
- **Manuals & Tutorials**: [http://spinroot.com/spin/Man/](http://spinroot.com/spin/Man/)
- **Examples**: See the [`Examples/`](file:///Volumes/External/Code/Spin/Examples) directory.
- **Documentation Papers & Books**: See the [`Doc/`](file:///Volumes/External/Code/Spin/Doc) directory.

---

## 📄 License

Spin is released under a BSD 3-Clause License. See [`LICENSE`](file:///Volumes/External/Code/Spin/LICENSE) for full details.


