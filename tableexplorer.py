
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

from typing import Optional

import os
import os.path
import zipfile

from collections import deque
import math
from z3 import Z3
from time import time
import random as rndm
import re

from components import Entry, BinaryRepr
from system import System
from table import Table

class TableExplorer:
    """ Table-based exploration.
    """
    
    def __init__(self, system: System, args) -> None:
        """ Initializer.
        """

        # A System and a Table
        self.system: System = system
        self.table = Table(args.output != "" and not args.check)

        # Input file
        self.input_file = os.path.basename(args.file)
            
        # Produce output?
        self.input_file = os.path.basename(args.file)
        self.output_file = args.output
        self.fill_table = None
        if self.output_file != "":
            self.fill_table = self.output_table
        else: self.fill_table = self.evaluate_table

        # Set closure of suffixes
        self.close = lambda v, r, b : self.close_prefixes(v, r, b)
        if args.signs:
            self.close = lambda v, r, b : self.close_prefixes_and_sign(v, r, b)
        elif args.suffixes: 
            self.close = lambda v, r, b : self.close_all(v, r, b)

        # To store the solver instance, initializations in compute_lower_bound
        self.solver: Optional[Z3]     = None
        self.time_limit: int          = args.time_limit

        # Parameter: number of solutions to be computed using the SMT solver before changing prefix
        self.max_nb_solutions: int = args.reset_pivot

        # Set how should the solver block solutions
        self.concrete_exec = args.concrete
        self.solver_block_solution = lambda a : self.solver_block_solution_abstract(a)
        if args.concrete:
            self.solver_block_solution = lambda a : self.solver_block_solution_concrete(a)

        # Number of times Z3 returned a solution
        self.counter_solutions: int   = 0

    
    def close_prefixes(self, v: BinaryRepr, row : Entry, next_it : bool): 
        for p in v.prefixes():
            self.table.add_row(self.system, p, row)
        a = self.table.add_column(self.system, v)
        if next_it : self.solver_block_solution(a)
        
    def close_all(self, v : BinaryRepr, row : Entry, next_it: bool): 
        right_derivs = set()
        for (p, s) in v.prefixes_and_suffixes():
            if p.size != 0: self.table.add_row(self.system, p, row)
            a = self.table.add_column(self.system, s)
            right_derivs.add(a)

        if next_it : 
            for a in right_derivs: 
                if self.system.evaluate(row, a) : 
                    self.solver_block_solution(a)
    
    def close_prefixes_and_sign(self, v: BinaryRepr, row : Entry, next_it : bool):
        for p in v.prefixes():
            self.table.add_row(self.system, p, row)
        a = self.table.add_column(self.system, v)
        s = self.table.add_column(self.system, v.sign_vector())
        if next_it : 
            self.solver_block_solution(a)
            self.solver_block_solution(s)
        

    def solver_block_solution_abstract(self, a: Entry):
        self.solver.write(self.system.block_solution(a))
        
    def solver_block_solution_concrete(self, c: Entry):
        for col in self.table.column_values.get_words(c):
            self.solver.write("(assert (or {}))\n".format(' '.join(["(distinct {} {})".format(var, val) for var, val in zip(self.system.variables, col.vec)])))

    def get_solution(self) -> Optional[BinaryRepr]:
        """ Return a solution for the SAT stack (BinaryRepr) and block it, or None if UNSAT.
        """

        if not self.solver.check_sat():
            return None

        model = self.solver.get_valuation()

        self.counter_solutions += 1

        return BinaryRepr([model[var] for var in self.system.variables])
    
    def init_solver_index(self, row: Entry) -> None:
        """ Assert S(x) <- psi(x) & (&_{c:T(r,c)} x != c),
            where psi(x) is a constraint system characterising {c in Sigma* : phi(r o c)}.
        """

        self.solver.reset()
        self.solver.write("(set-option :auto_config false)\n(set-option :smt.phase_selection 5)\n(set-option :smt.random_seed {})\n".format(rndm.randint(0, 4294967295)))
        self.solver.write(self.system.smt_lib_shift_rhs(row))

        for c in self.table.column_values.get():
            if self.system.evaluate(row, c):
                self.solver_block_solution(c)
                    
                prefixes = set()
                for val in self.table.column_values.get_words(c):
                    prefixes.update(val.prefixes())
                for p in prefixes:
                    self.table.add_row(self.system, p, row)

        
    def compute_lower_bound(self, debug: bool = False) -> None:
        """ Compute a lower bound of the number of states.
        """

        # Initalize solver
        self.solver = Z3(self.print_stats_and_evaluate, self.time_limit, debug)

        # Epsilon (empty vector)
        epsilon = BinaryRepr([0 for var in self.system.variables])
        epsilon.size = 0

        # Initialize table with a single row (epsilon)
        epsilon_derivative = self.table.add_row(self.system, epsilon)

        print("# Searching for prefixes and suffixes (timeout {:.2f} seconds)...".format(self.solver.timeout))

        def compute_lower_bound_loop():
            while not self.table.is_complete():
                
                row = epsilon_derivative
                if rndm.randrange(10) > 0:
                    row = self.table.row_oracle()

                self.init_solver_index(row)
                
                # Iterate over the max number of solutions
                it = 0
                max_it = max(self.max_nb_solutions-math.log2(self.table.row_values.num_active_elements()), 1 + math.log2(self.table.row_values.num_inactive_elements()+1))
                while it < max_it:
                    it = it+1

                    v = self.get_solution()

                    if v is None:
                        # Mark row as complete, since the last query was 'unsat'
                        self.table.set_row_complete(row)
                        break

                    self.close(v, row, it < max_it)

        compute_lower_bound_loop()

        if not self.concrete_exec:
            print("# Abstraction-based exploration completed")
            self.print_stats()
            
            print("\n# Resuming the exploration using concrete suffixes")
            
            self.table.row_values.start = 0
            self.solver_block_solution = lambda a : self.solver_block_solution_concrete(a)

            compute_lower_bound_loop()

        print("# Exploration completed")
        self.solver.kill()
        self.print_stats_and_evaluate()
        exit()

    def print_stats(self) -> None:
        """ Print the computed statistics.
        """
        print("# Number of prefixes:", self.table.row_values.num_elements(), "(closed: {})".format(self.table.row_values.num_inactive_elements()))
        print("# Number of suffixes:", len(self.table.column_values.get()))
        print("# Number of models computed by Z3:", self.counter_solutions)
        print("# Overall Z3 time: {:.2f} seconds".format(self.solver.compute_time))

    def evaluate_table(self) -> None:
        print("\n# Computing the lower bound (this step may require {} comparisons)...".format(re.sub(r'(?<!^)(?=(\d{3})+$)', r"'", str(self.table.row_values.num_elements()*len(self.table.column_values.get())))))
        t = time()

        rows = self.table.row_values.elements()
        cols = list(self.table.column_values.get())
        rndm.shuffle(cols)
        cols = tuple(cols)

        q = deque()

        res = 0

        if len(rows) <= 1 or len(cols) == 0:
            res = len(rows)
        else:
            q.append((0, len(rows), 0))

            # min_r = 0 
            # total = len(rows)
            # print("0%", end='\r')

            #Invariant: res + len(q) is a lower bound to the number of states 
            #The following loop refines q.
            while bool(q):
                (i, f, c) = q.pop()

                # if c > min_r:
                #    min_r = c
                #    print("{:.0%}".format(min_r/total), end='\r')

                (j, g) = (i, f)

                while j != g:
                    while j != g and not self.system.evaluate(rows[j], cols[c]): j = j+1 
                    
                    while j != g and self.system.evaluate(rows[g-1], cols[c]): g = g-1

                    if j != g:
                        g = g-1
                        rows[j], rows[g] = rows[g], rows[j]
                        j = j+1

                if j - i <= 1:
                    res = res + j - i 
                elif c + 1 == len(cols):
                    res = res + 1
                else: 
                    q.append((i,j,c+1))
                
                if f - g <= 1: 
                    res = res + f - g
                elif c + 1 == len(cols):
                    res = res + 1 
                else:
                    q.append((g,f,c+1))

        print("# Lower bound on the number of states:", res)
        print("# This computation took {:.2f} seconds".format(time() - t))
        print("")

    def output_table(self) -> None:
        print("\n# Computing the lower bound (this step may require {} comparisons)...".format(re.sub(r'(?<!^)(?=(\d{3})+$)', r"'", str(self.table.row_values.num_elements()*len(self.table.column_values.get())))))
        t = time()

        rows = self.table.row_values.elements()
        cols = list(self.table.column_values.get())
        rndm.shuffle(cols)
        cols = tuple(cols)

        used_cols = set()
        used_rows = set()

        if len(rows) <= 1 or len(cols) == 0:
            used_rows.update(self.table.row_repr[r] for r in rows)
        else:
            q = deque()
            q.append((0, len(rows), 0))

            while bool(q):
                (i, f, c) = q.pop()

                (j, g) = (i, f)

                while j != g:
                    while j != g and not self.system.evaluate(rows[j], cols[c]): j = j+1 
                    
                    while j != g and self.system.evaluate(rows[g-1], cols[c]): g = g-1

                    if j != g:
                        g = g-1
                        rows[j], rows[g] = rows[g], rows[j]
                        j = j+1

                if j - i == 0 or f - g == 0:
                    if c + 1 == len(cols): 
                        used_rows.add(self.table.row_repr[rows[i]])
                    else: 
                        q.append((i,f,c+1))
                else:
                    used_cols.add(min(self.table.column_values.get_words(cols[c])))

                    if j - i == 1 or c + 1 == len(cols):
                        used_rows.add(self.table.row_repr[rows[i]])
                    else: 
                        q.append((i,j,c+1))

                    if f - g == 1 or c + 1 == len(cols): 
                        used_rows.add(self.table.row_repr[rows[g]])
                    else:
                        q.append((g,f,c+1))

        print("# Lower bound on the number of states:", len(used_rows))
        print("# Number of suffixes used to prove this lower bound:", len(used_cols))
        print("# Storing certificate...")

        def in_chunks(l):
            chunk_len = 100000
            for i in range(0, len(l), chunk_len): 
                yield l[i:i + chunk_len]

        with zipfile.ZipFile(self.output_file, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            z.writestr('/data.info', "{{instance {}}}\n".format(self.input_file) + "{{lower-bound {}}}".format(len(used_rows)))
            i = 0
            for p_chunk in in_chunks(sorted(used_rows)):
                z.writestr('/data-' + str(i) + '.prefixes', "\n".join(str(row) for row in p_chunk))
                i = i + 1
            for s_chunk in in_chunks(sorted(used_cols)):
                z.writestr('/data-' + str(i) + '.suffixes', "\n".join(str(col) for col in s_chunk))
                i = i + 1

        print("# This computation took {:.2f} seconds".format(time() - t))

    def print_stats_and_evaluate(self) -> None:
        self.print_stats()
        self.fill_table()

    def parse(self, certificate_file: str):
        try:
            with zipfile.ZipFile(certificate_file, 'r') as zip_ref:
                proposed_lowerbound = None
                basename =  os.path.basename(certificate_file)
                print("# Extracting data from the certificate", basename)

                warning = ""

                # file_num = 0
                # total = len(zip_ref.namelist())
                # print("0%", end='\r')

                for file in zip_ref.namelist():
                    if file.endswith('.info'):
                        with zip_ref.open(file) as fp:
                            content = fp.read().decode('utf-8')
                            filename_match = re.search(r'\{instance ([^\}]+)\}', content)
                            if filename_match and filename_match.group(1).strip() != self.input_file:
                                warning = "# Warning: The input file does not match the instance string in the output file\n"
                                warning = warning + "# Input file: {}\n".format(self.input_file)
                                warning = warning + "# Instance string: {}".format(filename_match.group(1).strip())

                            lower_bound_match = re.search(r'\{lower-bound\s*(.*?)\s*\}', content)
                            if lower_bound_match:
                                proposed_lowerbound = int(lower_bound_match.group(1).strip().replace(' ',''))

                    if file.endswith('.prefixes'):
                        with zip_ref.open(file) as fp:
                            prefixes_tuples = re.findall(r'\((\d+),\((.*?)\)\)', fp.read().decode('utf-8').strip().replace(' ', ''), re.DOTALL)
                            for v, tuple_str in prefixes_tuples:
                                p = BinaryRepr()
                                p.size = int(v)
                                p.vec = tuple(map(int, tuple_str.split(',')))
                                self.table.add_row(self.system, p)

                    if file.endswith('.suffixes'):
                        with zip_ref.open(file) as fp:
                            suffixes_tuples = re.findall(r'\((\d+),\((.*?)\)\)', fp.read().decode('utf-8').strip().replace(' ', ''), re.DOTALL)
                            for v, tuple_str in suffixes_tuples:
                                s = BinaryRepr()
                                s.size = int(v)
                                s.vec = tuple(map(int, tuple_str.split(',')))
                                self.table.add_column(self.system, s)

                    # file_num = file_num + 1
                    # print("{:.0%}".format(file_num/total), end='\r')
                if warning != "": print(warning)

                if proposed_lowerbound is not None:
                    print("# Lower bound from certificate {}:".format(basename), proposed_lowerbound)

        except FileNotFoundError as e:
            exit(str(e))
