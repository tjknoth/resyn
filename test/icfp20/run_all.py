#!/usr/bin/python3
import sys
import os, os.path
import platform
import shutil
import time
import re
import difflib
import pickle
from subprocess import run, PIPE
from colorama import init, Fore, Back, Style
from statistics import median

# Globals
if platform.system() in ['Linux', 'Darwin']:
    SYNQUID_CMD = ['stack', 'exec', '--', 'resyn']              # Command to call Resyn
    TIMEOUT_CMD = ['timeout']                                   # Timeout command
    TIMEOUT = ['300']                                           # Timeout value (seconds)
else:
    SYNQUID_CMD = ['Resyn.exe']
    TIMEOUT_CMD = ['']
    TIMEOUT = ['']

LOGFILE = 'results.log'                                         # Log file
DUMPFILE = 'results'                                            # Result serialization file
CSV_FILE = 'results.csv'                                        # CSV-output file
LATEX_FILE = 'results.tex'                                      # Latex-output file
ORACLE_FILE = 'solutions'                                       # Solutions file
COMMON_OPTS = ['--print-stats']                                 # Options to use for all benchmarks
RESOURCE_OPTS = []
RESOURCES_OFF_OPT = ['-r=false']                                # Option to disable resource analysis
FNULL = open(os.devnull, 'w')                                   # Null file

PAPER_PATH = './'

class Benchmark:
    def __init__(self, name, description, options=[], np = '-'):
        self.name = name                # Id
        self.description = description  # Description (in the table)
        self.options = options          # Command-line options to use for this benchmark when running in individual context
        self.num_programs = np          # Number of programs generated in the enumerate-and-check process

    def str(self):
        return self.name + ': ' + self.description + ' ' + str(self.options)

class BenchmarkGroup:
    def __init__(self, name, default_options, benchmarks):
        self.name = name                        # Id
        self.default_options = default_options  # Command-line options to use for all benchmarks in this group when running in common context
        self.benchmarks = benchmarks            # List of benchmarks in this group

ALL_BENCHMARKS = [
    BenchmarkGroup("Quadratic", [], [
        Benchmark('List-Pairs', 'in-order pairs', ['-f=NONTERMINATING']),
        Benchmark('List-Reverse', 'list reverse', ['-f=NONTERMINATING']),
        Benchmark('List-Nub', 'remove duplicates', ['-f=NONTERMINATING']),
        Benchmark('List-InsertSort-Coarse', 'insertion sort (coarse)', ['-f=NONTERMINATING']),
        Benchmark('List-SelectionSort','selection sort', ['-f=NONTERMINATING']),
        # TODO: Benchmark('List-Merge-Sort-Quadratic','quadratic mergesort', ['-f=NONTERMINATING']),
        Benchmark('List-Quick-Sort-Quadratic','quadratic quicksort', ['-f=NONTERMINATING']),
        ]),
    BenchmarkGroup("Non-Polynomial", [], [
        Benchmark('List-Subset-Sum', 'subset sum problem', ['-f=NONTERMINATING']),
        # Benchmark('List-Merge-Build', 'merge sort build', ['-f=NONTERMINATING']),
        Benchmark('List-Merge-Flatten', 'merge sort flatten', ['-f=NONTERMINATING']),
        # Benchmark('List-Quick-Build', 'quick sort build', ['-f=NONTERMINATING']),
        # Benchmark('List-Quick-Flatten', 'quick sort flatten', ['-f=NONTERMINATING']),
        ]),
    BenchmarkGroup("Value-Dependent", [], [
        Benchmark('List-InsertSort', 'insertion sort (fine)', ['-f=NONTERMINATING', '--res-solver=CEGIS']),
        Benchmark('BST-Member', 'BT member', ['-f=NONTERMINATING']),
        Benchmark('BST-Insert', 'BT insert', ['-f=NONTERMINATING', '--res-solver=CEGIS'])
        ])
]

class SynthesisResult:
    def __init__(self, name, time, goal_count, code_size, spec_size, measure_count, num_constraints):
        self.name = name                        # Benchmark name
        self.time = time                        # Synthesis time (seconds)
        self.goal_count = goal_count            # Number of synthesis goals
        self.code_size = code_size              # Cumulative synthesized code size (in AST nodes)
        self.spec_size = spec_size              # Cumulative specification size (in AST nodes)
        self.measure_count = measure_count      # Number of measures defined
        self.optimized = False
        self.nres_code_size = '-'
        self.nres_time = -3.0
        self.eac_time = -3.0
        self.incremental_time = -3.0
        self.pct_slowdown = 0.0
        self.num_constraints = num_constraints

    def str(self):
        return self.name + ', ' + '{0:0.2f}'.format(self.time) + ', ' + self.goal_count + ', ' + self.code_size + ', ' + self.spec_size + ', ' + self.measure_count

def run_benchmark(name, opts, default_opts):
    '''Run benchmark name with command-line options opts (use default_opts with running the common context variant); record results in the results dictionary'''

    with open(LOGFILE, 'a+') as logfile:
      start = time.time()
      logfile.write(name + '\n')
      logfile.seek(0, os.SEEK_END)
      # Run Synquid on the benchmark:
      synthesis_res = run(TIMEOUT_CMD + TIMEOUT + SYNQUID_CMD + COMMON_OPTS + RESOURCE_OPTS + opts + [name + '.sq'], stdout=PIPE, stderr=PIPE, universal_newlines=True)
      end = time.time()

      print('{0:0.2f}'.format(end - start), end = ' ')
      if synthesis_res.returncode: # Synthesis failed
          print(Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL, end = ' ')
          synthesis_output = ''
          results [name] = SynthesisResult(name, (end - start), '-', '-', '-', '-', '-')
      else: # Synthesis succeeded: code metrics from the output and record synthesis time
          logfile.write(synthesis_res.stdout)
          lastLines = synthesis_res.stdout.split('\n')[-6:]
          synthesis_output = synthesis_res.stdout.split('\n')[:-6]
          goal_count = re.match("\(Goals: (\d+)\).*$", lastLines[0]).group(1)
          measure_count = re.match("\(Measures: (\d+)\).*$", lastLines[1]).group(1)
          spec_size = re.match("\(Spec size: (\d+)\).*$", lastLines[2]).group(1)
          solution_size = re.match("\(Solution size: (\d+)\).*$", lastLines[3]).group(1)
          num_constraints = re.match("\(Number of resource constraints: (\d+)\).*$", lastLines[4]).group(1)
          results [name] = SynthesisResult(name, (end - start), goal_count, solution_size, spec_size, measure_count, num_constraints)
          print(Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL, end = ' ')

      variant_options = [   # Command-line options to use for each variant of Synquid
            ('nres', opts + RESOURCES_OFF_OPT),
        ]

       #Run each variant: (now there's only one, should probably change this...)
      for (variant_id, opts) in variant_options:
          run_version(name, variant_id, opts, logfile, str(synthesis_output), results)

      print()

def set_eac_time(res, name, t):
    res[name].eac_time = t

def set_inc_time(res, name, t):
    res[name].incremental_time = t


def run_version(name, variant_id, variant_opts, logfile, with_res, results_file):
    '''Run benchmark name using command-line options variant_opts and record it as a Synquid variant variant_id in the results dictionary'''
    start = time.time()
    logfile.seek(0, os.SEEK_END)
    # Run Synquid on the benchmark, mute output:
    synthesis_res = run(TIMEOUT_CMD + TIMEOUT + SYNQUID_CMD + COMMON_OPTS +
        variant_opts + [name + '.sq'], stdout=PIPE, stderr=PIPE, universal_newlines=True)
    end = time.time()

    #results_file[name].eac_time = -1

    print('{0:0.2f}'.format(end - start), end = ' ')
    if synthesis_res.returncode == 124:  # Timeout: record timeout
      print(Back.RED + Fore.RED + Style.BRIGHT + 'TIMEOUT' + Style.RESET_ALL, end = ' ')
      results_file[name].nres_time = -1
    elif synthesis_res.returncode: # Synthesis failed: record failure
      print(Back.RED + Fore.RED + Style.BRIGHT + 'FAIL' + Style.RESET_ALL, end = ' ')
      results_file[name].nres_time = -2
    else: # Synthesis succeeded: record time for variant
      lastLines = synthesis_res.stdout.split('\n')[-6:]
      solution_size = re.match("\(Solution size: (\d+)\).*$", lastLines[3]).group(1)
      results_file[name].nres_time = (end - start)
      pct_slower = results_file[name].time / (end - start)
      results_file[name].pct_slowdown = pct_slower
      without_res = synthesis_res.stdout.split('\n')[:-6]
      # Compare outputs to see if resources led to any optimization
      diff = difflib.unified_diff(with_res, str(without_res))
      print(Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OK' + Style.RESET_ALL, end=' ')
      try:
          first = next(diff)
          if with_res != '': print(Back.GREEN + Fore.GREEN + Style.BRIGHT + 'OPTIMIZED' + Style.RESET_ALL, end=' ')
          results_file[name].optimized = True
          results_file[name].nres_code_size = solution_size
      except StopIteration:
          print('Unchanged', end=' ')

def format_time(t):
    if isinstance(t, str):
        return t
    elif t < 0:
        return '-'
    else:
        return '{0:0.2f}'.format(t)

def write_csv():
    '''Generate CSV file from the results dictionary'''
    with open(CSV_FILE, 'w') as outfile:
        for group in groups:
            for b in group.benchmarks:
                outfile.write (b.name + ',')
                result = results [b.name]
                optstr = 'True' if result.optimized else '-'
                outfile.write (result.spec_size + ',')
                outfile.write (result.code_size + ',')
                outfile.write (format_time(result.time) + ',')
                outfile.write (format_time(result.nres_time) + ',')
                outfile.write (result.nres_code_size + ',')
                #outfile.write (result.eac_time + ',')
                #outfile.write (optstr + ',')
                outfile.write ('\n')

def write_latex():
    '''Generate Latex table from the results dictionary'''

    total_count = 0
    to_def = 0
    to_nres = 0

    with open(LATEX_FILE, 'w') as outfile:
        for group in groups:
            outfile.write ('\multirow{')
            outfile.write (str(group.benchmarks.__len__()))
            outfile.write ('}{*}{\\parbox{1cm}{\\vspace{-0.85\\baselineskip}\center{')
            outfile.write (group.name)
            outfile.write ('}}}')

            for b in group.benchmarks:
                result = results [b.name]
                optstr = 'Yes' if result.optimized else '-'
                row = ( 
                    ' & ' + b.description + 
                    # ' & ' + result.goal_count + \
                    #' & ' + result.measure_count + \
                    ' & ' + result.code_size + 
                    ' & ' + format_time(result.time) + 
                    ' & ' + format_time(result.nres_time) + ' \\\\'
                    #' & ' + result.nres_code_size + \
                    #' & ' + str(b.num_programs) + \
                    #' & ' + format_time(result.eac_time) + ' \\\\'
                    #' & ' + optstr + ' \\\\'
                )
                outfile.write (row)
                outfile.write ('\n')

                total_count = total_count + 1
                if result.nres_time < 0.0:
                   to_nres = to_nres + 1

            outfile.write ('\\hline')

    print('Total:', total_count)
    print('TO nres:', to_nres)

def cmdline():
    import argparse
    a = argparse.ArgumentParser()
    a.add_argument('--medium', action='store_true')
    a.add_argument('--small', action='store_true')
    a.add_argument('--rerun', nargs=1, help='Rerun given benchmark')
    return a.parse_args()

if __name__ == '__main__':
    init()

    cl_opts = cmdline()

    # Check if there are serialized results
    if os.path.isfile(DUMPFILE):
        results = pickle.load(open(DUMPFILE, 'rb'))
    else:
        results = dict()

    # Delete old log file
    if os.path.isfile(LOGFILE):
      os.remove(LOGFILE)

    # Run experiments
    groups = ALL_BENCHMARKS[:1] if cl_opts.small else ALL_BENCHMARKS


    if cl_opts.rerun:
        bs = [b for g in groups for b in g if b.name == cl_opts.rerun[0]]
        for b in bs:
            print(b.str())
            run_benchmark(b.name, b.options, [])
            with open(DUMPFILE, 'wb') as data_dump:
                pickle.dump(results, data_dump)

    else:
        for group in groups:
            for b in group.benchmarks:
                if b.name in results:
                    print(b.str() + Back.YELLOW + Fore.YELLOW + Style.BRIGHT + 'SKIPPED' + Style.RESET_ALL)
                else:
                    print(b.str())
                    run_benchmark(b.name, b.options, group.default_options)
                    with open(DUMPFILE, 'wb') as data_dump:
                        pickle.dump(results, data_dump)

    med_slowdown = median([results[b.name].pct_slowdown for g in groups for b in g.benchmarks])
    print('Median slowdown = ' + str(med_slowdown))

    # Generate CSV
    write_csv()
    # Generate Latex table
    write_latex()

    # Compare with previous solutions and print the diff
    if os.path.isfile(ORACLE_FILE) and (not cl_opts.small):
        fromlines = open(ORACLE_FILE).readlines()
        tolines = open(LOGFILE, 'U').readlines()
        diff = difflib.unified_diff(fromlines, tolines, n=0)
        print()
        sys.stdout.writelines(diff)

    # Copy results to paper directory
    shutil.copy('./' + LATEX_FILE, PAPER_PATH + LATEX_FILE)
