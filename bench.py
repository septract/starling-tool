#!/usr/bin/env python3

import argparse
import collections
import os
import pathlib
import statistics
import sys
import platform
import timeit
from dataclasses import dataclass
from typing import Any, List, Optional, Mapping, DefaultDict, Union

from starling_common import *

# This file should contain records of the form
# descr:bucket:name:(grasshopper module path)
SPEC_FILE: str = 'bench.in'

# Number of times to run Z3 time benchmarks.
Z3_TIMES: int = 3

# Number of times to run GH time benchmarks.
GH_TIMES: int = 3

ARGS: Any = None


def example(value: Any) -> None:
    """Prints out an example description.

    Args:
        value: The value of the description.
    """
    print("#", value)


def fact(key: str, value: Any) -> None:
    """Prints out a benchmark fact.

    Args:
        key: The name of the fact to print.
        value: The value to print out.
    """
    print("  - ", key, ": ", value, sep="")


def loc(path: os.PathLike) -> int:
    """Gets the line count of the file at 'path'.

    Args:
        path: The path to the file to measure.

    Returns:
        The number of lines in the file at 'path'.
    """
    return sum(1 for _ in open(path))


def count_terms(starling: Starling, path: os.PathLike) -> Tuple[int, int]:
    """Runs Starling in Z3 mode on a file, and counts the outputted terms.

    Args:
        starling: The Starling object to use.
        path: The path to the Starling file to run.

    Returns:
        A pair of the total number of terms, and the number of
        those that generated an 'success' result from SMT
        elimination.
    """
    num_total: int = 0
    num_success: int = 0

    output: Output = starling.run_z3(path, extra_args=["-Btry-approx"])

    for line in output.stdout:
        _, sep, result = line.partition(':')
        if sep == '':
            continue

        num_total = num_total + 1

        is_success = result.strip() == 'success'
        num_success = num_success + 1 if is_success else num_success

    return num_total, num_success


@dataclass
class Z3TimeAnalysis:
    working_set: int
    total_time: float
    tool_time: float
    z3_time: float

def scrape_z3_times(lines: List[str]) -> Mapping[str, Mapping[str, List[float]]]:
    """Reads raw Z3 time analysis from a list of output lines.

    Args:
        lines: The list of lines from which we're scraping.

    Returns:
        The raw mapping of phases to metrics to time/memory observations.
    """
    # Accumulate metrics with a map from phase to metric to value,
    # auto-generating the map structure where it's missing.
    phases: Mapping[str, DefaultDict[str, List[float]]] = collections.defaultdict(
        lambda: collections.defaultdict(list)
    )

    for _ in range(Z3_TIMES):
        for line in lines:
            phase, sep, rest = line.partition(';')

            if sep == '':
                continue

            metric, _, value_raw = rest.partition(':')

            # This is always 'Phase XYZ': we want just 'XYZ'.
            phase = phase[6:]

            # The value sometimes comes with 'ms' on the end of it.
            # We don't want, or need, that.
            value_str : str = value_raw[:-2] if value_raw[-2:] == 'ms' else value_raw
            value: float = float(value_str)

            phases[phase.strip()][metric.strip()].append(value)

    return phases


def z3_times(starling: Starling, starling_path: os.PathLike) -> Z3TimeAnalysis:
    """Performs time and memory analysis on Starling/Z3.

    Args:
        starling: The Starling object to use.
        starling_path: The path to the Starling file.

    Returns:
        A tuple of the working set size, in KB; the total time
        spent in Starling; the time, of that, spent in the tool;
        and the time, of that, spent in Z3.
    """
    output: Output = starling.run_z3(starling_path, ["-Pphase-time,phase-working-set"])
    phases: Mapping[str, Mapping[str, List[float]]] = scrape_z3_times(output.stderr)

    # Working set is returned in KiB, but Starling emits in B.
    working_set_bytes: float = statistics.mean(phases['Eliminate']['WorkingSet'])
    working_set: int = int(working_set_bytes / 1024.0)

    # Times are emitted in milliseconds, so convert to seconds.
    elapsed_averages: Mapping[str, float] = {phase: statistics.mean(phases[phase]['Elapsed']) for phase in phases}

    # Total time is literally just sum of all phase times.

    total_time_micros: float = sum(elapsed_averages[phase] for phase in phases)
    total_time: float = total_time_micros / 1000.0

    # Time 'in Z3' is taken to be the eliminate phase.
    z3_time_micros: float = elapsed_averages['Eliminate']
    z3_time: float = z3_time_micros / 1000.0

    # Time 'on tool' is total time less Z3 time.
    tool_time: float = total_time - z3_time

    return Z3TimeAnalysis(working_set=working_set, total_time=total_time, tool_time=tool_time, z3_time=z3_time)


def proof_lines(starling_path: os.PathLike) -> Iterator[str]:
    """Yields the proof-carrying lines in a Starling file.

    This is a rough guess based on some string matching.

    Args:
        starling_path: The path to the Starling file.

    Yields:
        Each proof-carrying line.
    """
    view_nest: int = 0
    decl_nest: int = 0

    with open(starling_path) as f:
        for line in f:
            # TODO: This is very clumsy and ad-hoc.
            # Ideally Starling should be able to do this analysis
            # for us.

            in_proof = False

            view_nest = view_nest + line.count("{|")
            if view_nest > 0:
                in_proof = True
                view_nest = view_nest - line.count("|}")

            # Some comments in the current examples contain the
            # word 'constraints', which breaks this checker.
            # For now, insist on a space after 'constraint', etc.
            # This still over-reports proof LoC but not as much.
            decl_nest = (decl_nest +
                         line.count("constraint ") +
                         line.count("view "))
            if decl_nest > 0:
                in_proof = True
                decl_nest = decl_nest - line.count(";")

            if in_proof:
                yield line


def guess_proof_loc(starling_path: os.PathLike) -> int:
    """Guesses the lines of proof code in a Starling file.

    Args:
        starling_path: The path to the Starling file.

    Returns:
        A rough estimate of the lines of proof code.
    """
    return sum(1 for _ in proof_lines(starling_path))


@dataclass
class LocAnalysis:
    starling: int
    grass: Optional[int]
    proof: int


def count_loc(starling_path: os.PathLike, grass_path: Optional[os.PathLike]) -> LocAnalysis:
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
    starling_loc: int = loc(starling_path)
    grass_loc: Optional[int] = None if grass_path is None else loc(grass_path)
    proof_loc: int = 0 if grass_loc is None else grass_loc
    proof_loc = proof_loc + guess_proof_loc(starling_path)

    return LocAnalysis(starling_loc, grass_loc, proof_loc)


def make_grass_path(grass_name: str) -> Optional[pathlib.Path]:
    """If 'grass_name' is empty, returns None;
       otherwise, creates the full path to the GRASShopper example given by the name.

    Args:
        grass_name: The name of the GRASShopper example; can be empty, but can't be None.

    Returns:
        The full GRASShopper path, if appropriate.
    """
    return None if grass_name == '' else pathlib.Path('grasshopper', grass_name + '.spl')


def bench(starling: Starling, bucket: str, name: str, grass: str):
    """Performs benchmarking for one Starling example.

    Dumps results to stdout.

    Args:
        starling: The Starling object to use.
        bucket: The category (Pass, Fail, etc.) in which the example
            lives.
        name: The name, less the file extension, of the example.
        grass: The name of the GRASShopper auxiliary module.
            If empty, the example is taken to be a Z3 example.
    """

    starling_path: pathlib.Path = inflate_example_name(bucket, name)
    fact("Path", starling_path)

    grass_path: Optional[pathlib.Path] = make_grass_path(grass)

    is_grass: bool = grass_path is not None
    if (is_grass and ARGS.nogh) or (ARGS.noz3 and not is_grass):
        print("  *SKIPPED*")
        return

    fact("Mode", "GH" if is_grass else "Z3")

    line_counts: LocAnalysis = count_loc(starling_path, grass_path)
    fact("No. lines input", line_counts.starling)
    fact("No. lines auxiliary GRASShopper", "-" if line_counts.grass is None else line_counts.grass)
    fact("No. lines proof input", line_counts.proof)

    ntotal, nsuccess = count_terms(starling, starling_path)
    fact("No. generated terms", ntotal)
    fact("No. SMT-elim terms", nsuccess)

    z3: Z3TimeAnalysis = z3_times(starling, starling_path)
    fact("Time, total excl GH (s)", z3.total_time)
    fact("Time, on tool (s)", z3.tool_time)
    fact("Time, SMT (s)", z3.z3_time)
    fact("Mem use, Starling (KiB)", z3.working_set)

    if not is_grass:
        fact("No. lines gen GH", "-")
        fact("Time, GH (s)", "-")
        return

    # For GRASShopper, we can do the translation once, report the
    # LoC from that, and then run the last benchmarks directly
    # on GRASShopper alone.

    ghpath = starling.run_grasshopper_translate(starling_path)

    fact("No. lines gen GH", loc(ghpath))

    # This overestimates by adding Python overhead, but should be ok.
    ghtime = timeit.timeit('starling_common.run_and_cook(["grasshopper.native","' + os.fspath(ghpath) + '"])',
                           setup='import starling_common',
                           number=GH_TIMES)
    fact("Time, GH (s)", ghtime)

    ghpath.unlink()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-z', '--noz3', action='store_true', help='do not benchmark Z3 examples')
    parser.add_argument('-g', '--nogh', action='store_true', help='do not benchmark GRASShopper examples')
    ARGS = parser.parse_args()

    starling: Starling = get_starling()

    # TODO: Find out why this happens.
    if platform.system() == 'FreeBSD':
        print("WARNING: Memory usage metrics may be incorrectly reported as '0'.", file=sys.stderr)
        print("If this happens, try running eg. `command time -l ./starling.sh FILE`", file=sys.stderr)

    for desc, bucket, name, grass in read_infile(pathlib.Path(SPEC_FILE)):
        example(desc)
        bench(starling, bucket, name, grass)
