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
SPEC_FILE = './testresults'

Z3_SCRIPT = './starling.sh'
Z3_PASS_DIR = './Examples/Pass'
Z3_FAIL_DIR = './Examples/Fail'

GH_SCRIPT = './starling-gh.sh'
GH_PASS_DIR = './Examples/PassGH'
GH_FAIL_DIR = './Examples/FailGH'

CVF_RE = re.compile('^\S*\.cvf$')
ARGS = None

def verbose(fmt, *args):
    """Prints to stdout, but only in verbose mode."""
    if ARGS.verbose:
        print(fmt.format(*args))

def err(fmt, *args):
    """Prints to stderr."""
    print(fmt.format(*args), file=sys.stderr)

def run_and_get_stdout(script_name, file_name):
    """Runs script_name on file_name, returning the stdout lines as UTF-8."""
    p = subprocess.Popen([script_name, file_name], stdout=subprocess.PIPE)
    stdout = p.stdout.read()
    return stdout.decode('utf-8').split('\n')


def z3(file_name):
    """Runs Starling in Z3 mode on file_name, yielding all failing clauses."""
    # outputs in form
    # "clause_name: (success | fail)
    for line in run_and_get_stdout(Z3_SCRIPT, file_name):
        name, _, status = line.partition(':')
        name, status = name.strip(), status.strip()
        if status == 'fail':
            yield name

def grasshopper(file_name):
    """Runs Starling/GRASShopper mode on file_name, yielding failing clauses."""
    # The GRASShopper output needs some significant massaging.
    for line in run_and_get_stdout(GH_SCRIPT, file_name):
        pass

def make_failure_dict(spec_file):
    """Creates a lookup of all expected failures from spec_file.

    Returns a dict of (name: str -> failure_names: set[str])
    """
    expected_failures = {}

    with open(spec_file, 'r') as f:
        for line in f:
            name, _, failures = line.partition(':')
            name, failures = name.strip(), failures.strip()
            expected_failures[name] = set()
            for failure in failures.split(None):
                expected_failures[name].add(failure.strip())

    return expected_failures

def find(root, regexp):
    '''find all files under `root` that match regexp
    '''
    roots = collections.deque([root])
    while roots:
        root = roots.popleft()

        for root, dirs, files in os.walk(root):
            for file in files:
                if regexp.search(file):
                    yield os.path.join(root, file)

            for dir in dirs:
                roots.append(os.path.join(root, dir))

def check_z3(files, expected_failures):
    """Runs Starling/Z3 on each file in files, and reports failures."""
    failed_overall = False
    for file in files:
        verbose('check {}', file)

        if file not in expected_failures:
            err('[{}]', file)
            err('test data missing')
            return True

        failed = False
        for fail in z3(file):
            if fail not in expected_failures[file]:
                if not failed:
                    failed = True
                    err('[{}]', file)
                    err(' unexpected failures:', file)
                err('>  {}', fail)
                failed_overall = True

    return failed_overall

def main():
    ''' Run starling on the Examples/Pass and Examples/Fail directories
    and check that there are no unexpected failures. Exiting with exit code 1
    if there are
    '''
    expected_failures = make_failure_dict(SPEC_FILE)

    pass_z3 = find(Z3_PASS_DIR, CVF_RE)
    fail_z3 = find(Z3_FAIL_DIR, CVF_RE)
    failed = check_z3(itertools.chain(pass_z3, fail_z3), expected_failures)

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
    ARGS = parser.parse_args()
    main()
