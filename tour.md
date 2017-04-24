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

## Example Files

Figure 4 of the submitted paper mentions several benchmarked examples.
These correspond to the following invocations of Starling, with the
following files.

### SMT/Z3

These can be run using `starling.sh Examples/Pass/FILE`, where `FILE` is:

* ARC (static): `arc.cvf`
* Ticket lock (static): `ticketLock.cvf`
* Spinlock (static): `spinLock.cvf`
* Reader/writer lock: `singleWriterMultiReaderLock.cvf`
* Peterson’s algorithm: `petersonArray.cvf`

### GRASShopper

These can be run using `starling-gh.sh Examples/PassGH/FILE`, where `FILE` is:

* ARC (allocated): `arc.cvf`
* Ticket lock (allocated): `ticketLock.cvf`
* Spin lock (allocated): `spinLock.cvf`
* CLH queue-lock: `clhLock.cvf`
* Lock-coupling list: `lclist-module.cvf`

### Additional Examples

Starling also comes with additional examples in the `Pass` and `PassGH`
directories, most of which correspond to minor variations on the benchmarked
examples.

The `Fail` and `FailGH` directories contain failing examples, which can be
used to validate Starling's response to ill-formed proofs.  We also suggest
editing the passing scripts to add typoes and bugs, to exercise Starling's
error handling and failing proof behaviour.

### Validation

These assignments from benchmark name to file are tracked by the file
`benchmarks.in`, which tells the benchmark scripts which files to run.
`benchmarks.in` is commented.
