#!/usr/bin/env python
from __future__ import print_function

import argparse
import collections
import os
import string
import timeit

from starling_common import *

# This file should contain records of the form
# descr:bucket:name:(grasshopper module path)
SPEC_FILE = 'bench.in'

# Number of times to run Z3 time benchmarks.
Z3_TIMES = 3

# Number of times to run GH time benchmarks.
GH_TIMES = 3

ARGS = None


def example(value):
    """Prints out an example description.

    Args:
        value: The value of the description.
    """
    print("#", value)


def fact(key, value):
    """Prints out a benchmark fact.

    Args:
        key: The name of the fact to print.
        value: The value to print out.
    """
    print("  - ", key, ": ", value, sep="")

def loc(path):
    """Gets the line count of the file at 'path'.

    Args:
        path: The path to the file to measure.

    Returns:
        The number of lines in the file at 'path'.
    """
    return sum(1 for line in open(path))


def count_terms(starling_args, path):
    """Runs Starling in Z3 mode on a file, and counts the outputted terms.

    Args:
        starling_args: The list containing the Starling program
            and its arguments, eg. from get_starling().
        path: The path to the Starling file to run.
 
    Returns:
        A pair of the total number of terms, and the number of
        those that generated an 'success' result from SMT
        elimination.
    """
    ntotal, nsuccess = 0, 0

    lines, _ = run_starling_z3(starling_args, path,
                               extra_args=["-Btry-approx"])

    for line in lines:
        _, sep, result = line.partition(':')
        if sep == '':
            continue
        
        ntotal = ntotal + 1

        is_success = result.strip() == 'success'
        nsuccess = nsuccess + 1 if is_success else nsuccess

    return ntotal, nsuccess
    

def z3_times(starling_args, starling_path):
    """Performs time and memory analysis on Starling/Z3.

    Args:
        starling_args: The list containing the Starling program
            and its arguments, eg. from get_starling().
        starling_path: The path to the Starling file.

    Returns:
        A tuple of the working set size, in KB; the total time
        spent in Starling; the time, of that, spent in the tool;
        and the time, of that, spent in Z3.
    """

    # Accumulate metrics with a map from phase to metric to value,
    # auto-generating the map structure where it's missing.
    phases = collections.defaultdict(
        lambda: collections.defaultdict(list)
    )

    _, stderr = run_starling_z3(starling_args, starling_path,
                                ["-Pphase-time,phase-working-set"])

    for _ in range(Z3_TIMES):
        for line in stderr:
            phase, sep, rest = line.partition(';')

            if sep == '':
                continue

            metric, _, value = rest.partition(':')

            # This is always 'Phase XYZ': we want just 'XYZ'.
            phase = phase[6:]

            # The value sometimes comes with 'ms' on the end of it.
            # We don't want, or need, that.
            value = value[:-2] if value[-2:] == 'ms' else value
            value = float(value)

            phases[phase.strip()][metric.strip()].append(value)

    # Now, average across:
    for phase in phases:
        for metric in phases[phase]:
            phases[phase][metric] = (sum(phases[phase][metric])
                                     / len(phases[phase][metric]))
    
    # Working set is returned in KiB, but Starling emits in B.
    wset = long(phases['Eliminate']['WorkingSet'] / 1024)

    # Times are emitted in milliseconds, so convert to seconds.

    # Total time is literally just sum of all phase times.
    total = sum(phases[p]['Elapsed'] for p in phases) / 1000

    # Time 'in Z3' is taken to be the eliminate phase.
    inz3 = phases['Eliminate']['Elapsed'] / 1000

    # Time 'on tool' is total time less Z3 time.
    ontool = total - inz3

    return (wset, total, ontool, inz3)


def proof_lines(starling_path):
    """Yields the proof-carrying lines in a Starling file.

    This is a rough guess based on some string matching.

    Args:
        starling_path: The path to the Starling file.

    Yields:
        Each proof-carrying line.
    """
    view_nest = 0
    decl_nest = 0

    with open(starling_path) as f:
        for line in f:
            # TODO: This is very clumsy and ad-hoc.
            # Ideally Starling should be able to do this analysis
            # for us.

            in_proof = False

            view_nest = view_nest + string.count(line, "{|")
            if view_nest > 0:
                in_proof = True
                view_nest = view_nest - string.count(line, "|}")

            # Some comments in the current examples contain the
            # word 'constraints', which breaks this checker.
            # For now, insist on a space after 'constraint', etc.
            # This still over-reports proof LoC but not as much.
            decl_nest = (decl_nest +
                         string.count(line, "constraint ") +
                         string.count(line, "view "))
            if decl_nest > 0:
                in_proof = True
                decl_nest = decl_nest - string.count(line, ";")

            if in_proof:
                yield line


def proof_loc(starling_path):
    """Guesses the lines of proof code in a Starling file.

    Args:
        starling_path: The path to the Starling file.

    Returns:
        A rough estimate of the lines of proof code.
    """
    return sum(1 for l in proof_lines(starling_path))


def count_loc(starling_path, grass_path):
    """Performs lines of code analysis for one Starling example.

    Args:
        starling_path: The path to the Starling file.
        grass_path: The path to the GRASShopper auxiliary module.
            If None, the example is taken to be a Z3 example.

    Returns:
        A triple of:
            - Number of Starling input lines;
            - Number of GRASShopper input lines;
            - Number of proof input lines (guesstimate).
    """
    lstarling = loc(starling_path)
    lgh = "-" if grass_path is None else loc(starling_path)
    lproof = 0 if grass_path is None else lgh
    lproof = lproof + proof_loc(starling_path)
    
    return lstarling, lgh, lproof


def bench(starling_args, bucket, name, grass):
    """Performs benchmarking for one Starling example.

    Dumps results to stdout.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        bucket: The category (Pass, Fail, etc.) in which the example
            lives.
        name: The name, less the file extension, of the example.
        grass: The name of the GRASShopper auxiliary module.
            If empty, the example is taken to be a Z3 example.
    """

    starling_path = inflate_example_name(bucket, name)
    fact("Path", starling_path)

    grass_path = (None
                  if grass == ''
                  else os.path.join('grasshopper', grass + '.spl'))

    is_grass = grass_path is not None
    if (is_grass and ARGS.nogh) or (ARGS.noz3 and not is_grass):
        print("  *SKIPPED*")
        return

    fact("Mode", "GH" if is_grass else "Z3")

    lstarling, lgh, lproof = count_loc(starling_path, grass_path)
    fact("No. lines input", lstarling)
    fact("No. lines auxiliary GRASShopper", lgh)
    fact("No. lines proof input", lproof)

    ntotal, nsuccess = count_terms(starling_args, starling_path)
    fact("No. generated terms", ntotal)
    fact("No. SMT-elim terms", nsuccess)

    wset, ttotal, tontool, tinz3 = z3_times(starling_args, starling_path)
    fact("Time, total excl GH (s)", ttotal)
    fact("Time, on tool (s)", tontool)
    fact("Time, SMT (s)", tinz3)
    fact("Mem use, Starling (KiB)", wset)

    if not is_grass:
        fact("No. lines gen GH", "-")
        fact("Time, GH (s)", "-")
        return

    # For GRASShopper, we can do the translation once, report the
    # LoC from that, and then run the last benchmarks directly
    # on GRASShopper alone.

    ghpath = run_starling_grasshopper_translate(starling_args,
                                                starling_path)

    fact("No. lines gen GH", loc(ghpath))

    # This overestimates by adding Python overhead, but should be ok. 
    ghtime = timeit.timeit('starling_common.run_and_cook(["grasshopper.native","' + ghpath + '"])',
                           setup='import starling_common',
                           number=GH_TIMES)
    fact("Time, GH (s)", ghtime)

    os.unlink(ghpath)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-z', '--noz3', action='store_true', help='do not benchmark Z3 examples')
    parser.add_argument('-g', '--nogh', action='store_true', help='do not benchmark GRASShopper examples')
    ARGS = parser.parse_args()

    starling_args = get_starling()

    if os.name != 'posix' and not ARGS.nogh:
        print("WARNING: GRASShopper timing may fail on non-POSIX systems.")

    for desc, bucket, name, grass in read_infile(SPEC_FILE):
        example(desc)
        bench(starling_args, bucket, name, grass)
