# Starling

_Starling_ is an automated verification tool for concurrent programs.
It accepts programs written in a C-like language and annotated with
_Concurrent Views Framework_-style assertions, as well as a series
of constraints binding those assertions to concrete facts about the
program's shared state, and tries to prove soundness.

For a quick example of the flavour of Starling scripts, see
`Examples/Pass/ticketLock.cvf`.

## Current work

Starling is a work in progress, but currently it can check
correctness of fully-specified programs written in a limited command
language (integer and Boolean variables; basic statements; atomic
assignment and compare-and-swap; parameter-less methods with no
calling).

Examples of programs it can prove sound can be found in the
`Examples/Pass` directory; examples of programs it can prove unsound,
likewise, inhabit `Examples/Fail`.

## Future work

* Inference of constraints for unspecified view assertions, using
  backends such as HSF;
* Methods with call/return syntax;
* Compound data types (eg arrays, structs, ...);
* Proof of soundness of the tool itself;
* Clean-up and general user interface polish.

## Requirements

A F# 4.0 development environment (tested with mono on Linux),
NuGet, and the native Z3 library for your platform.

NuGet should be able to restore the rest of the prerequisites.

## Licence

MIT; see `LICENSE`.
