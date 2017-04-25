# Starling Tour

This 'guided tour' of Starling accompanies the Starling paper ('Lightweight
Concurrency with Views', CAV'2017 to appear), and is intended to allow
verification of the figures shown in that paper as well as the general
claims made in that paper.

**NOTE:** This tour is written for artifact evaluation against the preprint
version of the paper.  It may change when the final paper is submitted.


## Commands

From the `starling-tool` directory, the full list of available scripts is:

* `./starling.sh FILENAME`: Run Starling in Z3 mode on the given proof script,
  and output details of any failing proof terms.
* `./starling-gh.sh FILENAME`: Run Starling in GRASShopper mode, and print
  the GRASShopper output for the generated verification conditions.
* `python regress.py -v`: Run the Starling regression tests (described below).
* `unit.sh`: Run the Starling unit tests (described below).  `python bench.py`:
* `python bench.py`: Run proofs for the files described in _Example Files_ below,
  and print out benchmarks in a form similar to that in Figure 4 of
  the paper.

For information on the command-line arguments Starling supports, run
`./starling.sh -h`.


## Figure 1: Shared-variable ARC

This figure corresponds, with some minor changes, to the file
`Examples/Pass/arc.cvf`.  To check the proof, use
`./starling.sh Examples/Pass/arc.cvf`.


## Figure 2: Heap-allocated ARC

As above, this figure corresponds to `Examples/PassGH/arc.cvf`.  To check
this proof, use `./starling-gh.sh Examples/PassGH/arc.cvf`.

This proof includes an auxiliary GRASShopper file at
`grasshopper/arc-module.spl`.


## Figure 3: CLH Lock

The CLH lock proof is given in `Examples/PassGH/clhLock.cvf`, and an
auxiliary file at `grasshopper/clhLock-module.spl`.

Compared to the preprint, this proof has changed in several ways:

- The view atoms have been renamed, and `loose` split into two views,
  though the resulting assertions are essentially the same;
- A bug in the invariant definition has been found and corrected;
- Most of the auxiliary module has been inlined.

These changes are due to the CLH lock proof being used as an example
in workshop talks, and were made to make the CLH lock proof easier to
follow in such situations.


## Figure 4: Benchmarks

To run the entire benchmark suite used for Figure 4 of the paper, use
`bench.py` (requires Python 2.7).  This calls Starling and GRASShopper
several times, using Starling's built-in profiling support (and Python's
statement timing support for GRASShopper).

### Examples used in benchmarks

Assignments from benchmark name to file are tracked by the file
`bench.in`, which tells the benchmark scripts which files to run.
`bench.in` is commented.

The `bench.in` assignments used in the paper correspond to the following
invocations of Starling, with the following files:

**Note: There have been several minor syntactic changes made to the proof
scripts since the preprint.  These changes will be reflected in the final
paper.  These changes, as well as some alterations to the benchmark script,
account for the differences in lines of code figures from the preprint to
the artifact.**

#### SMT/Z3

These can be run using `starling.sh Examples/Pass/FILE`, where `FILE` is:

* ARC (static): `arc.cvf`
* Ticket lock (static): `ticketLock.cvf`
* Spinlock (static): `spinLock.cvf`
* Reader/writer lock: `singleWriterMultiReaderLock.cvf`
* Peterson’s algorithm: `petersonArray.cvf`

#### GRASShopper

These can be run using `starling-gh.sh Examples/PassGH/FILE`, where `FILE` is:

* ARC (allocated): `arc.cvf`
* Ticket lock (allocated): `ticketLock.cvf`
* Spin lock (allocated): `spinLock.cvf`
* CLH queue-lock: `clhLock.cvf`
* Lock-coupling list: `lclist-module.cvf`


## Appendix A

See Figure 3.


## Additional Examples

Starling also comes with additional examples in the `Pass` and `PassGH`
directories, most of which correspond to minor variations on the benchmarked
examples.

The `Fail` and `FailGH` directories contain failing examples, which can be
used to validate Starling's response to ill-formed proofs.  We also suggest
editing the passing scripts to add typoes and bugs, to exercise Starling's
error handling and failing proof behaviour.


## Test Suites

Starling comes with two test suites, both of which can be run using a single
command.

The unit tester, `unit.sh`, runs NUnit (if available) on a compiled copy of
Starling, and reports the number of passed and failed tests.  For AEC copies of
Starling, all tests should pass.

The regression tester, `regress.py`, is a wrapper around Starling that that
runs the tool on all of the example files, and checks the resulting failed
proof terms against a manifest, `regress.in`.  This manifest outlines the
expected failures, and is useful for checking that Starling is finding the
correct proof failures.


## Source Code

The Starling source code is contained in the `.fs` files in the root directory.
This is written in F#, a language similar to OCaml but based on the .NET
Framework.

Files of interest include:

* `Parser.fs`: the language parser, which is useful as a last resort guide to
  how the Starling language works;
* `Reify.fs`: implements most of the reification process described
  in section 3.2. `check` etc. implement the downclosure checks
  from section 3.3. `reifyView` implements actual reification;
* `Semantics.fs`: the function `markedMicrocodeToBool` and other nearby
  functions perform the conversion from Starling atomic commands to
  the two-state form described at the beginning of section 4;
* `TermGen.fs`: `minusViewByFunc` implements the view minus step
  briefly discussed in section 3.3;
* `Grasshopper.fs` and `Z3.fs`: the interfaces to the proof
  back-ends.  Z3 is tightly integrated into Starling using its C# bindings,
  while for GRASShopper we currently output a separate file to use as input to
  that proof tool.
