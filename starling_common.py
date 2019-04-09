"""Common definitions for regress.py and bench.py."""

import os
import re
import subprocess
import tempfile
import pathlib

# Top level examples directory.
from dataclasses import dataclass
from typing import List, Tuple, Optional, Iterator

EXAMPLES_DIR = 'Examples'

Z3_ARGS = ['-ssmt-sat']
GH_ARGS = ['-sgrass', '-Btry-approx']

# Used to match GRASShopper failures
GH_FAIL_RE = re.compile(r'^A postcondition of (?P<term>[^ ]+) might not hold at this return point$')


def inflate_example_name(bucket: str, name: str) -> pathlib.Path:
    """Creates an example filepath from its bucket and name.

    Args:
        bucket: The category (Pass, Fail, etc.) in which the example
            lives.
        name: The name, less the file extension, of the example.

    Returns:
        The inflated example filepath.
    """
    return pathlib.Path(EXAMPLES_DIR, bucket, (name + ".cvf"))


def read_infile(path: os.PathLike) -> Iterator[List[str]]:
    """Reads a colon-separated, hash-commented file.

    These are used both by regress.py and bench.py.

    Args:
        path: The path to the file to read.

    Yields:
        Each record in the file, as a list of fields.
    """
    with open(path, 'r') as f:
        for line in f:
            sline, _, _ = line.partition('#')
            if sline.strip() != '':
                yield [r.strip() for r in sline.split(':')]


@dataclass
class Output:
    """Contains cooked stdout and stderr lines."""
    stdout: List[str]
    stderr: List[str]


def run_and_cook(args: List[str]) -> Output:
    """Runs a process and returns its output as UTF-8 lines.

    Args:
        args: A list containing the program name, and zero or more arguments.

    Returns:
        The cooked, UTF-8 stdout and stderr lines.
    """
    proc = subprocess.Popen(args,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    stdout, stderr = proc.communicate()
    return Output(stdout=stdout.decode('utf-8').split('\n'),
                  stderr=stderr.decode('utf-8').split('\n'))


@dataclass
class Starling:
    """Represents a way of invoking Starling."""

    #  A list, where the zeroth element is the program to run, and all
    #  subsequent elements are arguments.
    args: List[str]

    def run_z3(self, path: os.PathLike, extra_args: Optional[List[str]] = None) -> Output:
        """Runs Starling in Z3 mode on path.

        Args:
            self: This object.
            path: The name of the file to check.
            extra_args: Any additional arguments to pass to Starling.

        Returns:
            The tuple of cooked, UTF-8 stdout and stderr lines.
        """
        all_z3_args = Z3_ARGS + ([] if extra_args is None else extra_args)
        return run_and_cook(self.args + all_z3_args + [os.fspath(path)])

    def run_grasshopper_translate(self, path: os.PathLike) -> pathlib.Path:
        """Runs Starling on path, translating it into GRASShopper.

        Args:
            self: This object.
            path: The name of the file to check.

        Returns:
            The name of the temporary file generated containing the
            GRASShopper input.
        """
        # GRASShopper can't read from stdin, so we have to make a temporary file.
        args : List[str] = self.args + GH_ARGS + [os.fspath(path)]
        # Having the current directory as dir is a nasty hack.
        with tempfile.NamedTemporaryFile(dir='', suffix='.spl', delete=False) as tempf:
            path = pathlib.Path(tempf.name)
            starling = subprocess.Popen(args, stdout=tempf)
            starling.wait()
        return path

    def run_grasshopper(self, grasshopper_args: List[str], path: os.PathLike) -> Output:
        """Runs Starling/GRASShopper mode on path.

        Args:
            self: This object.
            grasshopper_args: A list containing the program name, and zero or
                more arguments, needed to run GRASShopper.
            path: The name of the file to check.

        Returns:
            The tuple of cooked, UTF-8 stdout and stderr lines coming from
            GRASShopper (not Starling).
        """
        grass_path: pathlib.Path = self.run_grasshopper_translate(path)
        output = run_and_cook(grasshopper_args + [grass_path.name])
        grass_path.unlink()

        return output


def get_starling() -> Starling:
    """Tries to find the correct invocation for Starling on this platform.

    Returns:
        A Starling object that can be run to invoke Starling.
    """
    # This method used to do some platform-specific stuff, but now we just
    # assume the .NET Core runtime exists.
    return Starling(args=['dotnet', 'run', '--no-build', '--project', 'starling'])

