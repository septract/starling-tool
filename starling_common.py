"""Common definitions for regress.py and bench.py."""

import os
import re
import subprocess
import tempfile

# Top level examples directory.
EXAMPLES_DIR = 'Examples'

Z3_ARGS = ['-ssmt-sat']
GH_ARGS = ['-sgrass', '-Btry-approx']

# Used to match GRASShopper failures
GH_FAIL_RE = re.compile('^A postcondition of (?P<term>[^ ]+) might not hold at this return point$')


def inflate_example_name(bucket, name):
    """Creates an example filepath from its bucket and name.

    Args:
        bucket: The category (Pass, Fail, etc.) in which the example
            lives.
        name: The name, less the file extension, of the example.

    Returns:
        The inflated example filepath.
    """
    return os.path.join(EXAMPLES_DIR, bucket, (name + ".cvf"))


def read_infile(path):
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
                yield [ r.strip() for r in sline.split(':') ]


def get_starling():
    """Tries to find the correct invocation for Starling on this platform.

    Returns:
        A list, where the zeroth element is the program to run, and all
        subsequent elements are arguments.
    """

    # This method used to do some platform-specific stuff, but now we just
    # assume the .NET Core runtime exists.
    return ['dotnet', 'run', '--no-build', '--project', 'starling']


def run_and_cook(args):
    """Runs a process and returns its output as UTF-8 lines.

    Args:
        args: A list containing the program name, and zero or more arguments.

    Returns:
        The tuple of cooked, UTF-8 stdout and stderr lines.
    """
    proc = subprocess.Popen(args,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)
    stdout, stderr = proc.communicate()
    return (stdout.decode('utf-8').split('\n'),
            stderr.decode('utf-8').split('\n'))


def run_starling_z3(starling_args, path, extra_args=None):
    """Runs Starling in Z3 mode on path.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        path: The name of the file to check.
        extra_args: Any additional arguments to pass to Starling.

    Returns:
        The tuple of cooked, UTF-8 stdout and stderr lines.
    """
    zargs = Z3_ARGS + ([] if extra_args is None else extra_args)
    return run_and_cook(starling_args + zargs + [path])


def run_starling_grasshopper_translate(starling_args, path):
    """Runs Starling on path, translating it into GRASShopper.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        grasshopper_args: A list containing the program name, and zero or
            more arguments, needed to run GRASShopper.
        path: The name of the file to check.

    Returns:
        The name of the temporary file generated containing the
        GRASShopper input.
    """
    # GRASShopper can't read from stdin, so we have to make a temporary file.
    sargs = starling_args + GH_ARGS + [path]
    # Having the current directory as dir is a nasty hack.
    with tempfile.NamedTemporaryFile(dir='', suffix='.spl', delete=False) as tempf:
        sname = os.path.basename(tempf.name)
        starling = subprocess.Popen(sargs, stdout=tempf)
        starling.wait()
    return sname


def run_starling_grasshopper(starling_args, grasshopper_args, path):
    """Runs Starling/GRASShopper mode on path.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        grasshopper_args: A list containing the program name, and zero or
            more arguments, needed to run GRASShopper.
        path: The name of the file to check.

    Returns:
        The tuple of cooked, UTF-8 stdout and stderr lines coming from
        GRASShopper (not Starling).
    """
    sname = run_starling_grasshopper_translate(starling_args, path)
    stdout, stderr = run_and_cook(grasshopper_args + [sname])
    os.unlink(sname)

    return (stdout, stderr)
