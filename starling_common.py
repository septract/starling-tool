"""Common definitions for regress.py and bench.py."""

import os
import re
import subprocess
import tempfile

Z3_ARGS = ['-ssmt-sat']
GH_ARGS = ['-sgrass', '-Btry-approx']

# Used to match GRASShopper failures
GH_FAIL_RE = re.compile('^A postcondition of (?P<term>[^ ]+) might not hold at this return point$')


def get_starling():
    """Tries to find the correct invocation for Starling on this platform.

    Returns:
        A list, where the zeroth element is the program to run, and all
        subsequent elements are arguments.
    """

    # Assume the binary went in its usual location.
    path = os.path.join('bin', 'Debug', 'starling.exe')

    # On Windows, we can run .NET assemblies directly.
    if os.name == 'nt':
        return [path]

    # On other platforms, we assume we have access to mono.
    return ['mono', path]


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


def run_starling_z3(starling_args, file_name):
    """Runs Starling in Z3 mode on file_name.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        file_name: The name of the file to check.

    Returns:
        The tuple of cooked, UTF-8 stdout and stderr lines.
    """
    return run_and_cook(starling_args + Z3_ARGS + [file_name])


def run_starling_grasshopper(starling_args, grasshopper_args, file_name):
    """Runs Starling/GRASShopper mode on file_name.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        grasshopper_args: A list containing the program name, and zero or
            more arguments, needed to run GRASShopper.
        file_name: The name of the file to check.

    Returns:
        The tuple of cooked, UTF-8 stdout and stderr lines coming from
        GRASShopper (not Starling).
    """
    # GRASShopper can't read from stdin, so we have to make a temporary file.
    sargs = starling_args + GH_ARGS + [file_name]
    # Having the current directory as dir is a nasty hack.
    with tempfile.NamedTemporaryFile(dir='', suffix='.spl', delete=False) as tempf:
        sname = os.path.basename(tempf.name)
        starling = subprocess.Popen(sargs, stdout=tempf)
        starling.wait()

    stdout, stderr = run_and_cook(grasshopper_args + [sname])
    os.unlink(sname)

    return (stdout, stderr)
