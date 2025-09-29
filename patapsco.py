#!/usr/bin/env python3

"""
This file is part of Patapsco.

Patapsco is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Patapsco is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Patapsco. If not, see <https://www.gnu.org/licenses/>.
"""

from argparse import ArgumentParser
from logging import DEBUG, basicConfig, info
from system import System
from tableexplorer import TableExplorer
import random as rndm
import numpy as np
import os.path


def main():
    """ Main function.
    """
    np.seterr(over='raise',under='raise')

    # Arguments parser
    parser = ArgumentParser(description='Patapsco - Presburger Arithmetic To Automata Prober of State COmplexity')

    parser.add_subparsers(help='Mode', dest='sub_parsers')

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 1.0',
                        help="Show the version number and exit")

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="Increase output verbosity")

    parser.add_argument('-f', '--file',
                        type=str,
                        required=True,
                        help="Path to the formula file")

    parser.add_argument('-o', '--output',
                        type=str,
                        default="",
                        help="Write a certificate in output. If the argument is a dot, the output is named \"x.table\", where \"x\" is the name of the input file")   
    
    parser.add_argument('-c', '--certificate',
                        nargs='+', 
                        default=[],
                        help="Read one or more certificates. You can write a dot as an argument to check a certificate named \"x.table\", where \"x\" is the name of the input file")
    
    parser.add_argument('--check',
                        action='store_true',
                        help="Check the certificates. When providing this flag, the flags -o and --resume are ignored. This is the default behaviour when -f and -c are provided, but not -o nor --resume")
    
    parser.add_argument('--resume',
                        action='store_true',
                        help="Resume computation from the given certificates. This flag is ignored if --check is enabled. This is also the default behaviour when both -c and -o are given (but not --check). If -o is missing, no output certificate is produced")

    parser.add_argument('-d', '--debug',
                        action='store_true',
                        help="Print the SMT-LIB input/output")
    
    parser.add_argument('-t', '--time-limit',
                        action='store',
                        type=int,
                        default=1800,
                        help="Time limit for the computation done with Z3")
    
    parser.add_argument('--suffixes',
                        action='store_true',
                        help="Close columns of the table under suffixes. This may indirectly increase also the number of prefixes. Using this together with the option --concrete may slow down Z3 significantly.")
    
    parser.add_argument('--signs',
                        action='store_true',
                        help="Add sign vectors to columns. This flag is ignored if --suffixes is enabled.")
    
    parser.add_argument('--concrete',
                        action='store_true',
                        help="Use concrete suffixes when when calling Z3. Enable this option when coefficients in the system are large, or if you anticipate large solutions/suffixes (these may slow down Z3 significantly).")
    
    parser.add_argument('--seed',
                        action='store',
                        type=int,
                        default=-1,
                        help="Set the random seed")
    
    parser.add_argument('-r', '--reset-pivot',
                        action='store',
                        type=int,
                        default=10,
                        help="Advice the program on how many solutions should we search for a selected pivot")
    
    parser.add_argument('--stats',
                        action='store_true',
                        help="Prints statistics on the instance.")
    
    parser.add_argument('--only-stats',
                        action='store_true',
                        help="Prints statistics on the instance and exists.")
    
    args = parser.parse_args()

    # Set the verbose level
    if args.verbose:
        basicConfig(format="%(message)s", level=DEBUG)
    else:
        basicConfig(format="%(message)s")

    if args.sub_parsers == None: 
        args.sub_parsers = "table"

    args.certificate = set(args.certificate)
    if '.' in args.certificate:
        args.certificate.remove('.')
        args.certificate.add(os.path.basename(args.file) + ".table")

    if args.output == '.':
        args.output = os.path.basename(args.file) + ".table"

    # Set random seed

    a_seed = rndm.randint(0, 4294967295)
    if args.seed >= 0: a_seed = args.seed

    print("# Input file:", args.file)
    print("# Random seed:", a_seed)

    system = System(args.file)

    info("\n# Parsed system\n" + system.smt_lib() + "\n")

    rndm.seed(a_seed)

    table_explorer = TableExplorer(system, args)

    if args.check and len(args.certificate) == 0: 
        print("[Error] You must provide a certificate to check (option -c CERTIFICATE)")

    if args.stats or args.only_stats:  
        print()
        try:
            complexity = str(system.query_complexity())
        except OverflowError:
            complexity = "inf"
        print("# Query complexity:", complexity)
        print("# Number of variables:", system.num_variables())
        print("# Number of constraints:", system.num_constraints())
        print("# Average of integer constants: {:.2f}".format(system.avg_constants()))

    if args.only_stats:
        exit()
    
    elif args.check or (len(args.certificate) != 0 and args.output == "" and not args.resume): 
        print("# Checking certificate(s):", ', '.join(os.path.basename(cert) for cert in args.certificate))

        for certificate in args.certificate:
            table_explorer.parse(certificate)

        print("# Number of prefixes:", table_explorer.table.row_values.num_elements())
        print("# Number of suffixes:", len(table_explorer.table.column_values.get()))
        print("# Maximum length of a prefix:", table_explorer.table.max_prefix_size)
        table_explorer.evaluate_table()
    
    else:
        if len(args.certificate) != 0:
            print("# Resuming computation starting from:", ', '.join(os.path.basename(cert) for cert in args.certificate))
            for certificate in args.certificate:
                table_explorer.parse(certificate)
            print("# Number of extracted prefixes:", table_explorer.table.row_values.num_elements())
            print("# Number of extracted suffixes:", len(table_explorer.table.column_values.get()))
    
        if args.output != "":
            print("# Output file:", args.output)

        print("\n# [Lower bound computation]\n")
    
        if args.time_limit != 0:
            table_explorer.compute_lower_bound(args.debug)
    
        else: 
            print("# Generation of new prefixes and suffixes skipped (-t 0)")
            table_explorer.fill_table()



if __name__=='__main__':
    main()