#!/usr/bin/env python
from __future__ import print_function

import os
import re
import sys
import argparse
import itertools
import subprocess
import collections

# This file should contain records of the form
# filepath: failing-term1 failing-term2 ... failing-termN
SPEC_FILE = 'testresults'

Z3_ARGS = ['-ssmt-sat']
Z3_PASS_DIR = os.path.join('Examples', 'Pass')
Z3_FAIL_DIR = os.path.join('Examples', 'Fail')

GH_ARGS = []
GH_PASS_DIR = os.path.join('Examples', 'PassGH')
GH_FAIL_DIR = os.path.join('Examples', 'FailGH')

CVF_RE = re.compile('^\S*\.cvf$')
ARGS = None

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
        verbose('Running Windows, can execute {} directly.', path)
        return [path]

    # On other platforms, we assume we have access to mono.
    verbose('Not running Windows, will use Mono to execute {}.', path)
    return ['mono', path]

def verbose(fmt, *args):
    """Prints to stdout, but only in verbose mode."""
    if ARGS.verbose:
        print(fmt.format(*args))

def err(fmt, *args):
    """Prints to stderr."""
    print(fmt.format(*args), file=sys.stderr)

def run_and_get_stdout(script_name, script_args, file_name):
    """Runs script_name on file_name, returning the stdout lines as UTF-8."""
    args = [script_name] + script_args + [file_name]
    p = subprocess.Popen(args, stdout=subprocess.PIPE)
    stdout = p.stdout.read()
    return stdout.decode('utf-8').split('\n')


def z3(starling_args, file_name):
    """Runs Starling in Z3 mode on file_name, yielding all failing clauses.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        file_name: The name of the file to check.

    Yields:
        Each failing clause resulting from running Starling.
    """
    args = starling_args + Z3_ARGS + [file_name]

    for line in subprocess.check_output(args).decode('utf-8').split('\n'):
        # outputs in form
        # "clause_name: (success | fail)
        name, _, status = line.partition(':')
        name, status = name.strip(), status.strip()
        if status == 'fail':
            yield name

def grasshopper(starling_args, grasshopper_args, file_name):
    """Runs Starling/GRASShopper mode on file_name, yielding failing clauses.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        grasshopper_args: A list containing the program name, and zero or
            more arguments, needed to run GRASShopper.
        file_name: The name of the file to check.

    Yields:
        Each failing clause resulting from running Starling.
    """
    # The GRASShopper output needs some significant massaging.
    sargs = starling_args + GH_ARGS + [file_name]
    starling = subprocess.Popen(sargs, stdout=PIPE)

    grasshopper = subprocess.Popen(grasshopper_args, stdin=starling.stdout, stdout=subprocess.PIPE)

    starling.stdout.close()
    lines = starling.communicate()[0].decode('utf-8').split('\n')

    for line in lines:
        m = GH_FAIL_RE.match(line)
        if m:
            yield m.group('term')

def make_failure_dict(spec_file):
    """Creates a lookup of all expected failures from spec_file.

    Returns a dict of (name: str -> failure_names: set[str])
    """
    expected_failures = {}

    with open(spec_file, 'r') as f:
        for line in f:
            records = [ r.strip() for r in line.split(':') ]
            bucket, name, failures = records
            path = os.path.join('Examples', bucket, name)
            expected_failures[path] = set()
            for failure in failures.split(None):
                expected_failures[path].add(failure.strip())

    return expected_failures

def find(root, regexp):
    """find all files under `root` that match regexp
    """
    roots = collections.deque([root])
    while roots:
        root = roots.popleft()

        for root, dirs, files in os.walk(root):
            for file in files:
                if regexp.search(file):
                    yield os.path.join(root, file)

            for dir in dirs:
                roots.append(os.path.join(root, dir))

def check(files, checker, expected_failures):
    """Runs a checker on each file in files, and reports failures."""
    failed_overall = False
    for file in files:
        verbose('check {}', file)

        if file not in expected_failures:
            err('[{}]', file)
            err('test data missing')
            return True

        failed = False
        for fail in checker(file):
            if fail not in expected_failures[file]:
                if not failed:
                    failed = True
                    err('[{}]', file)
                    err(' unexpected failures:', file)
                err('>  {}', fail)
                failed_overall = True

    return failed_overall

def main():
    """ Run starling on the Examples/Pass and Examples/Fail directories
    and check that there are no unexpected failures. Exiting with exit code 1
    if there are
    """
    expected_failures = make_failure_dict(SPEC_FILE)
    starling_args = get_starling()

    failed = False

    if not ARGS.noz3:
        pass_z3 = find(Z3_PASS_DIR, CVF_RE)
        fail_z3 = find(Z3_FAIL_DIR, CVF_RE)
        z = lambda fn: z3(starling_args, fn)
        failed = check(itertools.chain(pass_z3, fail_z3), z, expected_failures)

    if not (failed or ARGS.nogh):
        pass_gh = find(GH_PASS_DIR, CVF_RE)
        fail_gh = find(GH_FAIL_DIR, CVF_RE)
        g = lambda fn: grasshopper(starling_args, ['grasshopper.native'], fn)
        failed = check(itertools.chain(pass_gh, fail_gh), g, expected_failures)

    if failed:
        verbose('')
        print('FAIL.')
        sys.exit(1)
    else:
        verbose('')
        print('OK.')
        sys.exit(0)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-v', '--verbose', action='store_true', help='turn on verbose output')
    parser.add_argument('-z', '--noz3', action='store_true', help='do not check Z3 examples')
    parser.add_argument('-g', '--nogh', action='store_true', help='do not check GRASShopper examples')
    ARGS = parser.parse_args()
    main()
