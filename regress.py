#!/usr/bin/env python
from __future__ import print_function

import os
import re
import sys
import argparse
import itertools
import collections
from starling_common import *

# This file should contain records of the form
# bucket:name: failing-term1 failing-term2 ... failing-termN
SPEC_FILE = 'regress.in'

Z3_PASS_DIR = os.path.join('Examples', 'Pass')
Z3_FAIL_DIR = os.path.join('Examples', 'Fail')

GH_PASS_DIR = os.path.join('Examples', 'PassGH')
GH_FAIL_DIR = os.path.join('Examples', 'FailGH')

CVF_RE = re.compile('^\S*\.cvf$')
ARGS = None

def verbose(fmt, *args):
    """Prints to stdout, but only in verbose mode."""
    if ARGS.verbose:
        print(fmt.format(*args))

def err(fmt, *args):
    """Prints to stderr."""
    print(fmt.format(*args), file=sys.stderr)

def z3(starling_args, file_name):
    """Runs Starling in Z3 mode on file_name, yielding all failing clauses.

    Args:
        starling_args: A list containing the program name, and zero or
            more arguments, needed to run Starling.
        file_name: The name of the file to check.

    Yields:
        Each failing clause resulting from running Starling.
    """
    lines, _ = run_starling_z3(starling_args, file_name)
    for line in lines:
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
    lines, _ = run_starling_grasshopper(starling_args, grasshopper_args, file_name)
    # The GRASShopper output needs some significant massaging.
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
            sline, _, _ = line.partition('#')
            if sline.strip() == '':
                continue

            records = [ r.strip() for r in sline.split(':') ]
            bucket, name, failures = records
            path = os.path.join('Examples', bucket, name) + ".cvf"
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
        g = lambda fn: grasshopper(starling_args, ['grasshopper.native', '-robust'], fn)
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
