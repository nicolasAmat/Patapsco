
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

from __future__ import annotations

from subprocess import PIPE, Popen
from typing import Optional
from time import time


class Z3:
    """ z3 interface.
    """

    def __init__(self, callback, timeout: int = 0, debug: bool = False) -> None:
        """ Initializer.
        """
        # Solver
        process = ['z3', '-in']
        self.timeout = timeout
        
        if timeout:
            process.append('-T:{}'.format(timeout))
            
        self.solver: Popen = Popen(process, stdin=PIPE, stdout=PIPE, start_new_session=True)

        # Flags
        self.debug: bool = debug

        # To track compute time 
        self.compute_time = 0
        
        # Callback function when z3 solver ends
        self.callback = callback

    def kill(self) -> None:
        """" Kill the process.
        """
        try:
            self.solver.kill()
        except ProcessLookupError:
            pass

    def abort(self) -> None:
        """ Abort the solver.
        """
        print("# Solver aborted")
        self.callback()
        self.kill()
        exit()

    def write(self, input: str, debug: bool = False) -> None:
        """ Write instructions to the standard input.
        """
        if self.debug or debug:
            print(input)

        if input != "":
            try:
                self.solver.stdin.write(bytes(input, 'utf-8'))
            except BrokenPipeError:
                self.abort()

    def flush(self) -> None:
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            self.abort()

    def readline(self, debug: bool = False):
        """ Read a line from the standard output.
        """
        self.compute_time = self.compute_time - time()
        try:
            smt_output = self.solver.stdout.readline().decode('utf-8').strip()
            if smt_output == 'timeout':
                self.compute_time = self.compute_time + time()
                self.abort()
            # assert("(error" not in smt_output)
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(smt_output)

        self.compute_time = self.compute_time + time()
        return smt_output

    def reset(self) -> None:
        """ Reset.

        Note
        ----
        Erase all assertions and declarations.
        """
        self.write("(reset)\n")

    def push(self):
        """ Push.

        Note
        ----
        Creates a new scope by saving the current stack size.
        """
        self.write("(push)\n")

    def pop(self) -> None:
        """ Pop.

        Note
        ----
        Removes any assertion or declaration performed between it and the last push.
        """
        self.write("(pop)\n")

    def check_sat(self) -> Optional[bool]:
        """ Check the satisfiability of the current stack of z3.
        """
        self.write("(check-sat)\n")
        self.flush()

        sat = self.readline()

        if sat == 'sat':
            return True
        elif sat == 'unsat':
            return False

        # TODO: Handle unknown. At the moment, (parsing) errors or timeout are all "None".
        return None

    def get_valuation(self) -> dict[str, int]:
        """ Get a valuation (assigment that satisfies the system) from the current SAT stack.
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '( '
        self.readline()

        # Parse the model
        model: dict[str, int] = {}
        
        while True:
            line = self.readline()

            content = line.split(' ')
            
            # Check if parsing done
            if len(content) < 2:
                break

            value = self.readline().replace(' ', '').replace(')', '').replace('(', '')
            variable = content[1]

            model[variable] = int(value)

        if not model:
            self.abort()

        return model
    
    def get_state(self, n: int) -> list[int]:
        """ Get a (reachable) state (of dimension n) from the current SAT stack.
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '( '
        self.readline()

        # Parse the model
        model = [0 for _ in range(n)]
        
        while True:
            content = self.readline().split(' ')

            # Check if parsing done
            if len(content) < 2:
                break

            value = self.readline().replace(' ', '').replace(')', '').replace('(', '')
            variable = content[1]

            if variable[0] == "x":
                index = int(variable.replace('x', ''))
                model[index] = int(value)

        return model