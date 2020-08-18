#!/usr/bin/python3
import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
import subprocess
from colorama import init, Fore, Back, Style

# Parameters
SYNQUID_PATH_LINUX = ['stack', 'exec', '--', 'resyn']
SYNQUID_PATH_WINDOWS = ['Resyn.exe']
BENCH_PATH = '.'
LOGFILE_NAME = 'results.log'
ORACLE_NAME = 'oracle'
OUTFILE_NAME = 'results.csv'
COMMON_OPTS = []
TIMEOUT_COMMAND = 'timeout'
TIMEOUT= '120'

SECTIONS = ['.', 'sygus', 'rbt', 'AVL']
RESOURCE_FALSE = ['-r=false']

BENCHMARKS = {
  '.' : [
              # Integers
              ('Int-Add',     []),
              # Lists
              ('List-Null',       []),
              ('List-Elem',       []),
              ('List-Stutter',    []),
              ('List-Replicate',  []),
              ('List-Append',     []),
              ('List-Concat',     []),
              ('List-Take',       []),
              ('List-Drop',       []),
              ('List-Delete',     []),
              ('List-Map',        []),
              ('List-ZipWith',    []),
              ('List-Zip',        []),
              ('List-ToNat',      ['-m 0']),
              ('List-Product',    []),
              ('List-ExtractMin',     ['-a=2', '-m 3']),
              ('List-Intersection',   []),
              ('List-Fold',           []),
              ('List-Fold-Length',    ['-m=0']),
              ('List-Fold-Append',    ['-m=0']),
              ('List-Ith',            []),
              ('List-ElemIndex',      []),
              ('List-Snoc',           []),
              ('List-Reverse',        []),
              # ('List-Range',          []),
              # ('List-Filter',         ['-g=False']),
              # Unique lists
              ('UniqueList-Insert',   []),
              ('UniqueList-Delete',   []),
              ('UniqueList-Range',    []),
              ('List-Nub',            []),
              ('List-Compress',       []),
              # Insertion sort
              ('List-InsertSort',     []),
              ('List-Fold-Sort',      ['-m=1', '-a=2', '--explicit-match']),
              # Merge sort
              ('List-Split',          ['-m=3']),
              ('IncList-Merge',       ['-f=AllArguments']),
              ('IncList-MergeSort',   ['-a=2', '-m=3']),
              # Quick sort
              ('List-Partition',      []),
              ('IncList-PivotAppend', []),
              ('IncList-QuickSort',   ['-a=2']),
              # Trees
              ('Tree-Elem',           []),
              ('Tree-Flatten',        []),
              # Binary search tree
              ('BST-Member',          []),
              ('BST-Insert',          []),
              ('BST-ExtractMin',      ['-a=2', '-m=3']),
              ('BST-Delete',          []),
              ('BST-Sort',            []),
              # Binary heap
              ('BinHeap-Member',      []),
              ('BinHeap-Insert',      []),
              # User-defined datatypes
              ('Evaluator',           []),
              ('AddressBook-Make',    ['-a=2']),
              ('AddressBook-Merge',   ['-a=2']),
              # Synthesis from examples
              ('Replicate-Examples',  []),
           ],
  'sygus' : [
              ('Int-Max2',    []),
              ('Int-Max3',    []),
              ('Int-Max4',    []),
              ('Int-Max5',    []),
              ('Array-Search-2', []),
              ('Array-Search-3', []),
              ('Array-Search-4', []),
              ('Array-Search-5', []),
              ('Array-Search-6', []),
            ],
  'AVL' : [
              # AVL trees
              ('AVL-BalL0',           ['-a 2']),
              ('AVL-BalLL',           ['-a 2', '-u']),
              ('AVL-BalLR',           ['-a 2', '-u']),
              ('AVL-BalR0',           ['-a 2']),
              ('AVL-BalRL',           ['-a 2', '-u']),
              ('AVL-BalRR',           ['-a 2', '-u']),
              ('AVL-Balance',         ['-a 2', '--explicit-match']),
              ('AVL-Insert',          ['-a 2']),
              ('AVL-ExtractMin',      ['-a 2']),
              ('AVL-Delete',          ['-a 2', '-m 1']),
          ],
  'rbt' : [
    # Red-black trees
    ('RBT-BalanceL',        ['-a 2', '-u']),
    ('RBT-BalanceR',        ['-a 2', '-u']),
    ('RBT-Insert',          ['-a 2', '-m 1']),
          ]
}

# RBT_BENCHMARKS = [
    # # Red-black trees
    # ('RBT-BalanceL',        ['-a 2', '-m 1', '-z']),
    # ('RBT-BalanceR',        ['-a 2', '-m 1', '-z']),
    # ('RBT-Insert',          ['-a 2', '-m 1', '-z']),
# ]

CHECKING_BENCHMARKS = [
    ('List-Append',         []),
    ('List-Replicate',      []),
    ('List-ToNat',          []),
    ('AVL',                 []),
]

DEMO_BENCHMARKS = [
    ('BST-Insert',          []),
    ('Holes',               []),
    ('List-Replicate',      []),
    ('List-Reverse',        []),
    ('NNF',                 []),
    ('Sort-Fold',           ['-m 1', '-a 2', '--explicit-match']),
]

UNIT_TESTS = [
    ('Constructors',         []),
    ('Pairs',                []),
    ('HigherOrder',          []),
    ('TypeAbduction',        []),
    ('Measure',              []),
    ('Instantiation',        []),
    ('MultiArgMeasure',      []),
    ('HOChecking',           []),
    ('Incr',                 []),
]

RESOURCE_VERIFICATION_BENCHMARKS = [
    ('BST-Contains',                 ['-f=Nonterminating']),
    ('List-Append2',                 ['-f=Nonterminating']),
    ('List-Append',                  ['-f=Nonterminating']),
    ('List-Compress',                ['-f=Nonterminating']),
    ('List-Cons2',                   ['-f=Nonterminating']),
    ('List-Pairs',                   ['-f=Nonterminating']),
    ('List-Reverse',                 ['-f=Nonterminating']),
    ('List-Replicate',               ['-f=Nonterminating', '--res-solver=CEGIS']),
    ('List-InsertSort-Coarse',       ['-f=Nonterminating']),
    ('List-Subset-Sum',              ['-f=Nonterminating']),
    ('List-InsertSort',              ['-f=Nonterminating', '--res-solver=CEGIS']),
    ('List-InsertSort-Compares',     ['-f=Nonterminating']),
    ('BST-Insert',                   ['-f=Nonterminating', '--res-solver=CEGIS']),
]

RESOURCE_INFERENCE_POS_BENCHMARKS = [
    # res verif benches
    ('BST-Contains',                 ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Append2',                 ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Append',                  ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Compress',                ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Cons2',                   ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Reverse',                 ['--eac', '--infer', '-f=Nonterminating']),
    ('List-InsertSort-Coarse',       ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Subset-Sum',              ['--eac', '--infer', '-f=Nonterminating']),
    ('List-InsertSort',              ['--eac', '--infer', '-f=Nonterminating', '--res-solver=CEGIS']),
    ('List-InsertSort-Compares',     ['--eac', '--infer', '-f=Nonterminating']),

    # RAML
    ('RAML-BitVec',                  ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-SizeChange',              ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-Lists',                   ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-Queue',                   ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-BinaryCounter',           ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-Compress',                ['--eac', '--infer', '-f=Nonterminating']),

    # ICFP '20 benches
    # Quadratic
    ('List-Nub', ['--eac', '--infer', '-f=NONTERMINATING']),

    # Non-Polynomial
    # ('List-Quick-Build', ['--eac', '--infer', '-f=NONTERMINATING']),
    ('List-Quick-Flatten', ['--eac', '--infer', '-f=NONTERMINATING']),
]

RESOURCE_INFERENCE_NEG_BENCHMARKS = [
    ('BST-Insert',                   ['--eac', '--infer', '-f=Nonterminating', '--res-solver=CEGIS']),
    ('BST-Member',                   ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Pairs',                   ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Exp-Contrived',           ['--eac', '--infer', '-f=Nonterminating']),
    ('List-Replicate',               ['--eac', '--infer', '-f=Nonterminating', '--res-solver=CEGIS']),

    # ICFP '20 benches
    # Quadratic
    ('List-Quick-Sort-Quadratic',    ['--eac', '--infer', '-f=NONTERMINATING']),
    ('List-SelectionSort',        ['--eac', '--infer', '-f=NONTERMINATING']),
    ('List-Merge-Sort-Quadratic', ['--eac', '--infer', '-f=NONTERMINATING']),

    # Non-Polynomial
    ('List-Merge-Sort', ['--eac', '--infer', '-f=NONTERMINATING']),
    ('List-Merge-Build', ['--eac', '--infer', '-f=NONTERMINATING']),
    ('List-Merge-Flatten', ['--eac', '--infer', '-f=NONTERMINATING']),

    # RAML
    ('RAML-SplitAndSort',            ['--eac', '--infer', '-f=Nonterminating']),
    ('RAML-Dyadic',                  ['--eac', '--infer', '-f=Nonterminating']),
]

RESOURCE_SYNTHESIS_BENCHMARKS = [
    ('BinHeap-Insert',      []),
    ('BST-Delete',          []),
    #('BST-ExtractMin',      []),
    ('BST-Insert',          []),
    ('BST-Member',          []),
    ('BST-Sort',            []),
    ('IncList-Merge',       ['-f=AllArguments']),
    #('IncList-MergeSort',   ['-a=2', '-m=3']),
    ('IncList-Pivot',       []),
    ('Int-Add',             []),
    ('List-Append',         []),
    # Without AllArguments it'll synthesize different slow implementations
    ('List-Intersect',      ['-f=AllArguments', '--backtrack']),
    #('List-Compare',        []),
    ('List-Compress',       []),
    ('List-Concat',         []),
    ('List-Cons2',          []),
    ('List-Delete',         []),
    ('List-Stutter',        []),
    ('List-Drop',           []),
    ('List-Elem',           []),
    ('List-ElemIndex',      []),
    ('List-ExtractMin',     ['-a=2', '-m=3']),
    ('List-Insert',         []),
    ('List-Ith',            []),
    ('List-Nub',            []),
    ('List-Null',           []),
    ('List-Partition',      []),
    ('List-Replicate',      []),
    ('List-Reverse',        []),
    #('Queue-Dequeue',       []),
    #('Queue-Enqueue',       []),
    ('List-Snoc',           []),
    ('List-Zip',            []),
    ('Tree-Flatten',        []),
    ('UniqueList-Delete',   []),
    ('UniqueList-Insert',   []),
    ('UniqueList-Range',    [])
]

class SynthesisResult:
    def __init__(self, name, time):
        self.name = name
        self.time = time

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', '

def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--resyn', help='resyn command')
    a.add_argument('--nr', action='store_true', help='disable resource analysis')
    a.add_argument('--unit', action='store_true', help='run unit tests')
    a.add_argument('--check', action='store_true', help='run type checking tests')
    a.add_argument('--synt', action='store_true', help='run synthesis tests')
    a.add_argument('--sections', nargs="*", choices=SECTIONS + ['all'], default=['all'], help=('which synthesis tests to run'))
    a.add_argument('--demo', action='store_true', help='run demo tests')
    a.add_argument('--res-verif', action='store_true', help='run resource-aware verification tests')
    a.add_argument('--res-infer', action='store_true', help='run resource inference tests')
    a.add_argument('--res-synth', action='store_true', help='run resource-aware synthesis tests')
    a.add_argument('--optimize', action='store_true', help='Check if ReSyn improved performance of Synquid-generated code' )
    return a.parse_args()

def printerr(str):
    print (Back.RED + Fore.BLACK + Style.BRIGHT + str + Style.RESET_ALL, end = ' ')

def printok(str):
    print (Back.GREEN + Fore.BLACK + Style.BRIGHT + str + Style.RESET_ALL, end = ' ')

def printwarn(str):
    print (Back.YELLOW + Fore.YELLOW + Style.BRIGHT + str + Style.RESET_ALL, end = ' ')

def run_benchmark(name, opts, path='.', neg=False):
    global total_time
    print (name + "(bad)" if neg else name, end=' ')

    with open(LOGFILE_NAME, 'a+') as logfile:
        start = time.time()
        logfile.seek(0, os.SEEK_END)
        return_code = subprocess.call(synquid_path + COMMON_OPTS + opts + [os.path.join (path, name + '.sq')], stdout=logfile, stderr=logfile)
        end = time.time()

        t = end - start
        print ('{0:0.2f}'.format(t), end=' ')
        total_time = total_time + t
        if (bool(return_code) ^ neg):
            printerr("FAIL")
        else:
            printok("OK")
            results [name] = SynthesisResult(name, t)
        print()

def run_resyn_benchmark(name, opts, path='.'):
    global total_time
    print (name, end=' ')

    with open(LOGFILE_NAME, 'a+') as logfile:
        start = time.time()
        with_res = subprocess.run(synquid_path + COMMON_OPTS + opts + [os.path.join (path, name + '.sq')], stderr=subprocess.STDOUT, stdout=subprocess.PIPE, universal_newlines=True)
        res_end = time.time()
        without_res = subprocess.run(synquid_path + COMMON_OPTS + RESOURCE_FALSE + opts + [os.path.join(path, name + '.sq')], stderr=subprocess.STDOUT, stdout=subprocess.PIPE, universal_newlines=True)
        end = time.time()
        rtime = res_end - start
        print ('{0:0.2f}'.format(rtime), end=' ')
        total_time = total_time + rtime

        logfile.seek(0, os.SEEK_END)
        logfile.write(with_res.stdout)
        if with_res.returncode:
          printerr("FAIL")
        else:
          printok("OK")
        diff = difflib.unified_diff(with_res.stdout, without_res.stdout)
        # Check if diff is empty
        try:
            first = next(diff)
            printok('Optimized')
            print()
        except StopIteration:
            print('Unchanged')


def write_times(benchmarks):
    with open(OUTFILE_NAME, 'w') as outfile:
        for (name, args) in benchmarks:
            outfile.write (name + ',')
            if name in results:
                res = results [name]
                outfile.write ('{0:0.2f}'.format(res.time))
                outfile.write (',')
            outfile.write ('\n')

def check_diff ():
    print()
    if not os.path.isfile(ORACLE_NAME):
        # Create oracle
        printwarn('Oracle file not found, creating a new one')
        shutil.copyfile(LOGFILE_NAME,ORACLE_NAME)
    else:
        # Compare log with oracle
        fromlines = open(ORACLE_NAME).readlines()
        tolines = open(LOGFILE_NAME).readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)

        # Check if diff is empty
        try:
            first = next(diff)
            printerr('TESTS FAILED WITH DIFF')
            print()
            print(first)
            sys.stdout.writelines(diff)
            print()
            return True

        except StopIteration:
            printok('TESTS PASSED')
            print()
            return False

def clear_log():
    if os.path.isfile(LOGFILE_NAME):
        os.remove(LOGFILE_NAME)


if __name__ == '__main__':
    init()
    results = {}
    total_time = 0

    a = cmdline()

    # Determine the synquid command to use:
    if a.resyn:
        synquid_path = a.resyn
    if platform.system() in ['Linux', 'Darwin']:
        synquid_path = SYNQUID_PATH_LINUX
    else:
        synquid_path = SYNQUID_PATH_WINDOWS

    # By default enable all tests:
    if not (a.unit or a.check or a.synt or a.demo or a.res_verif or a.res_infer or a.res_synth):
      a.unit = True
      a.check = True
      a.synt = True

    sections = [s.lower() for s in a.sections]
    try:
        os.chdir('test')
    except Exception:
        pass
    fail = False
    if a.unit:
        # Run unit tests
        os.chdir('unit')
        print(os.getcwd())
        clear_log()
        # for name in os.listdir('.'):
        #    filename, file_extension = os.path.splitext(name)
        #    if file_extension == '.sq':
        #        run_test(filename)
        for (name, args) in UNIT_TESTS:
            run_benchmark(name, args)
        fail = check_diff()
        os.chdir('..')

    if not fail and a.check:
        # Run type checking benchmarks
        os.chdir('checking')
        clear_log()
        for (name, args) in CHECKING_BENCHMARKS:
            args += RESOURCE_FALSE
            run_benchmark(name, args)
        fail = check_diff()
        os.chdir('..')

    if not fail and a.demo:
        # Test online demos
        os.chdir('demo')
        clear_log()
        for (name, args) in DEMO_BENCHMARKS:
            args += RESOURCE_FALSE
            run_benchmark(name, args)
        fail = check_diff()
        os.chdir('..')

    if not fail and a.res_verif:
        # Run resource-aware verification tests
        os.chdir('resources/verification')
        clear_log()
        for (name, args) in RESOURCE_VERIFICATION_BENCHMARKS:
            run_benchmark(name, args, 'pos')
            run_benchmark(name, args, 'neg', True)
        fail = check_diff()

        os.chdir('../..')

    if not fail and a.res_infer:
        # Run resource inference tests
        os.chdir('resources/inference')
        clear_log()
        for (name, args) in RESOURCE_INFERENCE_POS_BENCHMARKS:
            run_benchmark(name, args, 'pos')
        for (name, args) in RESOURCE_INFERENCE_NEG_BENCHMARKS:
            run_benchmark(name, args, 'neg', True)
        fail = check_diff()

        os.chdir('../..')

    if not fail and a.res_synth:
        # Run resource-aware synthesis tests
        os.chdir('resources/synthesis')
        clear_log()
        for (name, args) in RESOURCE_SYNTHESIS_BENCHMARKS:
            if a.optimize:
                run_resyn_benchmark(name, args)
            else:
                run_benchmark(name, args)
        fail = check_diff()
        os.chdir('../..')

    if not fail and a.synt:
        # Run synthesis benchmarks in 'current' directory
        os.chdir('current')
        clear_log()
        for sec in SECTIONS:
            if sec in sections or 'all' in sections:
                for (name, args) in BENCHMARKS[sec]:
                    if a.nr:
                        args += RESOURCE_FALSE
                    run_benchmark(name, args, sec)

        print('TOTAL', '{0:0.2f}'.format(total_time))

        if sections == ['all']:
            write_times(sum(BENCHMARKS.values(), []))
            check_diff()
        os.chdir('..')


