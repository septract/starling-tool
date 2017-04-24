# Starling Tour

This 'guided tour' of Starling accompanies the Starling paper
('Lightweight Concurrency with Views', CAV'2017 to appear), and is intended
to allow verification of the claims in that paper.

**NOTE:** This tour is written for artifact evaluation against the preprint
version of the paper.  It may change when the final paper is submitted.

## Commands

From the `starling-tool` directory, the full list of available scripts is:

* `starling.sh FILENAME`: Run Starling in Z3 mode on the given proof script,
  and output details of any failing proof terms.
* `starling-gh.sh FILENAME`: Run Starling in GRASShopper mode, and output
  the GRASShopper output for the generated verification conditions.
* `python -v regress.py`: Run the Starling regression tests (described below).
* `unit.sh`: Run the Starling unit tests (described below).
* `bench.sh`: Run proofs for the files described in _Example Files_ below,
  and print out benchmarks for them in a form similar to that in Figure 4
  of the paper.

For information on the command-line arguments Starling supports, run
`starling.sh -h`.

## Figure 4: Benchmarks

To run the entire benchmark suite used for Figure 4 of the paper,
use `bench.sh`.

To see how Starling's benchmark system runs, read `bench.sh` and its
included files.  These are written in POSIX shell language and the
`awk` text transformer tool.  We give pointers for further scrutiny
below.

### Examples used in benchmarks

Assignments from benchmark name to file are tracked by the file
`benchmarks.in`, which tells the benchmark scripts which files to run.
`benchmarks.in` is commented.

The `benchmarks.in` assignments used in the paper correspond to the
following invocations of Starling, with the following files:

**Note: There have been several minor syntactic changes made to the
proof scripts since the preprint.  Also, a bug in the CLH
lock proof was found and corrected after submission.  These changes
will be reflected in the final paper.**

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

## Additional Examples

Starling also comes with additional examples in the `Pass` and `PassGH`
directories, most of which correspond to minor variations on the benchmarked
examples.

The `Fail` and `FailGH` directories contain failing examples, which can be
used to validate Starling's response to ill-formed proofs.  We also suggest
editing the passing scripts to add typoes and bugs, to exercise Starling's
error handling and failing proof behaviour.

## Test Suites

Starling comes with two test suites, both of which can be
run using a single command.

The unit tester, `unit.sh`, runs NUnit (if available) on
a compiled copy of Starling, and reports the number of
passed and failed tests.  For AEC copies of Starling, all
tests should pass.

The regression tester, `regress.py`, is a wrapper around
`starling.sh` and `starling-gh.sh` that runs those scripts
on all of the example files, and checks the resulting failed
proof terms against a manifest, `testresults`.  This manifest
outlines the expected failures, and is useful for checking
that Starling is finding the correct proof failures.

## Source Code

The Starling source code is contained in the `.fs` files in
the root directory.  This is written in F#, a language
similar to OCaml but based on the .NET Framework.

Files of interest include:

* `Parser.fs`: the language parser, which is useful as a lasy
  resort guide to how the Starling language works;
* `Grasshopper.fs` and `Z3.fs`: the interfaces to the proof
  back-ends.  Z3 is tightly integrated into Starling using its
  C# bindings, while for GRASShopper we currently output a
  separate file to use as input to that proof tool.
