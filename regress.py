#!/usr/bin/env python
from __future__ import print_function

import os
import re
import sys
import argparse
import itertools
import subprocess
import collections

CVF_RE = re.compile('^\S*\.cvf$')
ARGS = None

def verbose(fmt, *args):
    ''' printf

    Only prints in verbose mod
    '''
    if ARGS.verbose:
        print(fmt.format(*args))

def err(fmt, *args):
    ''' printfe
    '''
    print(fmt.format(*args), file=sys.stderr)

def starling(file_name):
    ''' Yields all failing clauses from file_name
    '''
    p = subprocess.Popen(['./starling.sh', file_name], stdout=subprocess.PIPE)
    stdout = p.stdout.read()

    # outputs in form
    # "clause_name: (success | fail)
    for line in stdout.decode('utf-8').split('\n'):
        name, _, status = line.partition(':')
        name, status = name.strip(), status.strip()
        if status == 'fail':
            yield name

def make_failure_dict():
    '''Creates a lookup of all expected failures from "testresults"
    returning a dict of (name: str -> failure_names: set[str])
    '''
    expected_failures = {}

    with open('testresults', 'r') as f:
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

def main():
    ''' Run starling on the Examples/Pass and Examples/Fail directories
    and check that there are no unexpected failures. Exiting with exit code 1
    if there are
    '''
    found_unexpected_failure = False
    expected_failures = make_failure_dict()

    pass_z3 = find('./Examples/Pass', CVF_RE)
    fail_z3 = find('./Examples/Fail', CVF_RE)

    for file in itertools.chain(pass_z3, fail_z3):
        verbose('check {}', file)
        failed = False
        for fail in starling(file):
            if fail not in expected_failures[file]:
                if not failed:
                    failed = True
                    err('[{}]', file)
                    err(' unexpected failures:', file)
                err('>  {}', fail)
                found_unexpected_failure = True

    if found_unexpected_failure:
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
