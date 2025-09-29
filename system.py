
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

from abc import ABC, abstractmethod
from components import BinaryRepr, Entry
import numpy as np
import math
import operator
from pysmt.smtlib.parser import SmtLibParser
from pysmt.operators import (AND, OR, NOT, IMPLIES, IFF, INT_CONSTANT, SYMBOL, PLUS, MINUS, TIMES, LE, LT, EQUALS, ITE)
from pysmt.oracles import get_logic
from pysmt.exceptions import PysmtTypeError
from pysmt.rewritings import PrenexNormalizer
import sys
from typing import Optional

sys.setrecursionlimit(15000)


class System:
    """ (Full) Quantifier-Free Linear Integer Arithmetic (QF-LIA).
    """

    def __init__(self, filename: str) -> None:
        """ Initializer.
        """
        self.variables: list[str] = []
        self.indexes: dict[str, int] = {}
        
        self.n: int = 0
        self.m: int = 0

        self.A_eq = None
        self.c_eq = None
        self.nb_eq: int = 0

        self.A_ineq = None
        self.c_ineq = None
        self.nb_ineq: int = 0

        self.c: list[int] = []

        self.logic = None

        self.booleans: list[str] = []
        self.atoms: dict[str, int] = {}
        self.boolean_assertion: Optional[Formula] = None
        self.parse(filename)
        
        if self.boolean_assertion is not None:
            self.logic = AndOperator([self.logic, self.boolean_assertion])

        self.str_A: list[str] = []
        self.operators: list[str] = []
        self.builtin_ops: list[any] = []
        self.precompute()

    def __str__(self) -> str:
        def helper(a, c, operator):
            left = []
            for i, coef in enumerate(a):
                if coef:
                    left.append(str(coef) + '.' + self.variables[i])
            return ' + '.join(left) + ' {} '.format(operator) + str(c)

        return self.logic.__str__([helper(a, c, '=') for a, c in zip(self.A_eq, self.c_eq)] + [helper(a, c, '<=') for a, c in zip(self.A_ineq, self.c_ineq)])

    def num_variables(self) -> int: 
        return self.n 
    
    def num_constraints(self) -> int: 
        return self.m
    
    def avg_constants(self) -> float:
        sum_coeff = 0

        if self.m == 0: return 0

        for a, c in zip(self.A_eq, self.c_eq):
            sum_coeff += abs(c) + sum([abs(v) for v in a]) + 2            

        for a, c in zip(self.A_ineq, self.c_ineq):
            sum_coeff += abs(c) + sum([abs(v) for v in a]) + 2

        return sum_coeff / (self.m*(self.n+1))

    def query_complexity(self) -> int:
        """ Return the complexity of the instance.
        """
        product = 1

        for a, c in zip(self.A_eq, self.c_eq):
            product *= abs(c) + sum([abs(v) for v in a]) + 2            

        for a, c in zip(self.A_ineq, self.c_ineq):
            product *= abs(c) + sum([abs(v) for v in a]) + 2
            
        return math.ceil(math.log10((2 ** self.m) * product))

    def smt_lib(self, state=None) -> str:
        """ Assert the formula into the SMT-LIB format.
        """
        if state is None:
            state = self.c

        declaration = '\n'.join(map(lambda var: "(declare-fun {} () Int)".format(var), self.variables))
        return declaration + "\n(assert " + self.logic.smt_lib(["({} {} {})".format(operator, lhs, int(c)) if c is not None else "false" for lhs, operator, c in zip(self.str_A, self.operators, state)]) + ")\n"

    def smt_lib_shift_rhs(self, constants: Entry) -> str:
        """ Constraint system characterizing {x in Sigma* : S(r o x)}.
        """
        return self.smt_lib(state=constants)

    def block_solution(self, rhs: Entry) -> str:
        """ Block a given solution.
        """
        return "(assert (or {}))\n".format(' '.join(["(distinct {} {})".format(lhs, c) for lhs, c in zip(self.str_A, rhs)]))

    def evaluate(self, left_deriv : Entry, right_deriv : Entry) -> bool:
        """ Evaluate 'right_deriv <= left_deriv'.
        """
        return self.logic.evaluate([op(r, l) if l is not None else False for (r, op, l) in zip(right_deriv, self.builtin_ops, left_deriv)])

    def compute_left_derivative(self, x : BinaryRepr, custom_rhs : Optional[Entry] = None) -> Entry:
        """ Return the reached state by reading x from the initial state.
        """
        if x.size == 0: 
            return tuple(self.c)

        if custom_rhs is None: 
            custom_rhs = self.c

        eq_deriv = ()
        if self.nb_eq:
            none_indices = [i for i, v in enumerate(custom_rhs) if v is None]
            custom_rhs = [v if i not in none_indices else 0 for i, v in enumerate(custom_rhs)]
            eq_deriv = tuple(np.divide(np.subtract(custom_rhs[:self.nb_eq], np.dot(self.A_eq, x.vec)), (2**x.size)))
            eq_deriv = [v if v.is_integer() and i not in none_indices else None for i, v in enumerate(eq_deriv)]

        ineq_deriv = tuple(np.floor_divide(np.subtract(custom_rhs[self.nb_eq:], np.dot(self.A_ineq, x.vec)), (2**x.size))) if self.nb_ineq else ()
        return tuple(eq_deriv) + tuple(ineq_deriv)
    
    def compute_right_derivative(self, x : BinaryRepr) -> Entry:
        """ Return the reached state by reading x from the initial state.
        """
        eq_deriv = tuple(np.dot(self.A_eq, x.vec)) if self.nb_eq else ()
        ineq_deriv = tuple(np.dot(self.A_ineq, x.vec)) if self.nb_ineq else ()
        return eq_deriv + ineq_deriv

    def parse(self, filename: str) -> None:
        parser = SmtLibParser()
        with open(filename, 'r') as fp:
            script = parser.get_script(fp)
            try:
                formula = script.get_strict_formula()
            except PysmtTypeError:
                print("# Error: input file not compatible with the pySMT library")
                exit()
            
            normalizer = PrenexNormalizer()
            _, matrix = normalizer.walk(formula)
            self.parse_variables(matrix)
            self.parse_atoms(matrix)

            self.logic = self.parse_logic(matrix)
            self.atoms = {}
            self.booleans = []

            print("\n# Detected logic:", get_logic(formula))
    
    def parse_variables(self, formula):
        vars = formula.get_free_variables()
        for var in vars:
            var_str = var._content.payload[0]
            self.variables.append(var_str)
            if var._content.payload[1].is_bool_type():
                self.booleans.append(var_str)
        self.indexes = {v: i for i, v in enumerate(self.variables)}
        self.n = len(self.variables)

    def parse_atoms(self, formula) -> None:
        A_eq, c_eq, A_ineq, c_ineq = [], [], [], []
        nb_eq, nb_ineq = 0, 0

        atoms = formula.get_atoms()
        for atom in atoms:
            atom_str = atom.serialize()
            if atom_str not in self.atoms:

                if atom.node_type() == SYMBOL:
                    # atom is a boolean predicate
                    a = [0 for _ in range(self.n)]
                    a[self.indexes[atom._content.payload[0]]] = 1

                    A_eq.append(a)
                    c_eq.append(1)
                    self.atoms[atom_str] = (EQUALS, nb_eq)
                    nb_eq += 1
                else:
                    # Arithmetic comparison operators must be LE, LT, EQUALS
                    assert(atom.node_type() in [LE, LT, EQUALS])

                    a_left, c_left = self.parse_arithmetic(atom._content.args[0])
                    a_right, c_right = self.parse_arithmetic(atom._content.args[1])
                    if atom.node_type() == LT:
                        c_right = c_right - 1

                    a = [0 for _ in range(self.n)]
                    for k, v in a_left.items():
                        a[self.indexes[k]] += v
                    for k, v in a_right.items():
                        a[self.indexes[k]] -= v

                    if atom.node_type() == EQUALS:
                        A_eq.append(a)
                        c_eq.append(c_right - c_left)
                        self.atoms[atom_str] = (EQUALS, nb_eq)
                        nb_eq += 1
                    else:
                        A_ineq.append(a)
                        c_ineq.append(c_right - c_left)
                        self.atoms[atom_str] = (LE, nb_ineq)
                        nb_ineq += 1

        self.update_booleans(A_eq, c_eq)

        self.A_eq, self.c_eq = np.array(A_eq).astype(object), np.array(c_eq).astype(object)
        self.A_ineq, self.c_ineq = np.array(A_ineq).astype(object), np.array(c_ineq).astype(object)

        self.c = np.array(c_eq + c_ineq).astype(object)
        self.nb_eq, self.nb_ineq = len(c_eq), len(c_ineq)
        self.m = self.nb_eq + self.nb_ineq

    def update_booleans(self, A_eq, c_eq):
        disjuncts = []

        for var in self.booleans:
            a_true, a_false = [0 for _ in range(self.n)], [0 for _ in range(self.n)]

            index = len(A_eq)

            a_true[self.indexes[var]] = 1
            A_eq.append(a_true)
            c_eq.append(1)

            a_false[self.indexes[var]] = 1
            A_eq.append(a_false)
            c_eq.append(0)

            disjuncts.append(OrOperator([Atom(index), Atom(index + 1)]))

        if disjuncts:
            self.boolean_assertion = AndOperator(disjuncts)

    def precompute(self):
        def helper(a, str_operator, builtin_op):
            sum_x = []
            for var, coef in zip(self.variables, a):
                if coef:
                    sum_x.append("(* {} {})".format(coef, var) if coef != 1 else var)
                #if coef  == 1: sum_x.append(var)
                #elif coef > 1: sum_x.append("(* {} {})".format(coef, var))
                #elif coef < 0: sum_x.append("(* (- {}) {})".format(-coef, var))
            if sum_x:
                if len(sum_x) == 1:
                    self.str_A.append(sum_x[0])
                else:
                    self.str_A.append("(+ {})".format(' '.join(sum_x)))
            else:
                self.str_A.append("0")
            self.operators.append(str_operator)
            self.builtin_ops.append(builtin_op)

        for a in self.A_eq:
            helper(a, '=', operator.eq)

        for a in self.A_ineq:
            helper(a, '<=', operator.le)

    def parse_arithmetic(self, expr) -> tuple[dict[str, int], int]:
        a, c = None, None

        # PLUS
        if expr.node_type() == PLUS:
            a, c = self.parse_arithmetic(expr._content.args[0])
            for e in expr._content.args[1:]:
                a_, c_ = self.parse_arithmetic(e)
                a = { k: a.get(k, 0) + a_.get(k, 0) for k in a.keys() | a_.keys()}
                c = c + c_

        # MINUS
        elif expr.node_type() == MINUS:
            a, c = self.parse_arithmetic(expr._content.args[0])
            for e in expr._content.args[1:]:
                a_, c_ = self.parse_arithmetic(e)
                a = { k: a.get(k, 0) - a_.get(k, 0) for k in a.keys() | a_.keys()}
                c = c - c_

        # TIMES
        elif expr.node_type() == TIMES:
            a, c = self.parse_arithmetic(expr._content.args[0])
            for e in expr._content.args[1:]:
                a_, c_ = self.parse_arithmetic(e)
                assert not a or not a_
                if a:
                    a = { k: v * c_ for k, v in a.items()}
                elif a_:
                    a = { k: v * c for k, v in a_.items()}
                c = c * c_

        # SYMBOl
        elif expr.node_type() == SYMBOL:
            return {expr._content.payload[0] : 1}, 0
        
        # INT_CONSTANT
        elif expr.node_type() == INT_CONSTANT:
            return {}, expr._content.payload
        
        else:
            assert False

        return a, c

    def parse_logic(self, expr) -> Formula:
        if expr.node_type() == AND:
            return AndOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() == OR:
            return OrOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() == NOT:
            return NotOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() == IFF:
            return IffOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() == ITE:
            return IteOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() == IMPLIES:
            return ImpliesOperator([self.parse_logic(e) for e in expr._content.args])
        elif expr.node_type() in [EQUALS, LE, LT, SYMBOL]:
            op, i = self.atoms[expr.serialize()] 
            return Atom(i if op == EQUALS else self.nb_eq + i)
        else:
            assert False


class Formula(ABC):
    @abstractmethod
    def __str__(self, atoms_res: list[str]) -> str:
        pass

    @abstractmethod
    def smt_lib(self, atoms_res: list[str]) -> str:
        pass

    @abstractmethod
    def evaluate(self, atoms_res: list[bool]) -> bool:
        pass


class Atom(Formula):
    def __init__(self, index):
        self.index = index

    def __str__(self, atoms_res: list[str]) -> str:
        return atoms_res[self.index]

    def smt_lib(self, atoms_res: list[str]) -> str:
        return atoms_res[self.index]

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return atoms_res[self.index]


class BooleanOperator(Formula):
    def __init__(self, operands):
        self.operands: list[Formula] = operands

    
class AndOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "(" + ' & '.join(map(lambda e: e.__str__(atoms_res), self.operands)) + ")"

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(and {})".format(' '.join(map(lambda e: e.smt_lib(atoms_res), self.operands)))

    def evaluate(self, atoms_res: list[str]) -> bool:
        return all(map(lambda e: e.evaluate(atoms_res), self.operands))


class OrOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "(" + ' | '.join(map(lambda e: e.__str__(atoms_res), self.operands)) + ")"

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(or {})".format(' '.join(map(lambda e: e.smt_lib(atoms_res), self.operands)))

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return any(map(lambda e: e.evaluate(atoms_res), self.operands))


class NotOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "(! {})".format(self.operands[0].__str__(atoms_res))

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(not {})".format(self.operands[0].smt_lib(atoms_res))

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return not self.operands[0].evaluate(atoms_res)


class IffOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "({} <-> {})".format(self.operands[0].__str__(atoms_res), self.operands[1].__str__(atoms_res))

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(= {} {})".format(self.operands[0].smt_lib(atoms_res), self.operands[1].smt_lib(atoms_res))

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return self.operands[0].evaluate(atoms_res) == self.operands[1].evaluate(atoms_res)


class ImpliesOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "({} -> {})".format(self.operands[0].__str__(atoms_res), self.operands[1].__str__(atoms_res))

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(=> {} {})".format(self.operands[0].smt_lib(atoms_res), self.operands[1].smt_lib(atoms_res))

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return not self.operands[0].evaluate(atoms_res) or self.operands[1].evaluate(atoms_res)   


class IteOperator(BooleanOperator):
    def __str__(self, atoms_res: list[str]) -> str:
        return "({} ? {} : {})".format(self.operands[0].__str__(atoms_res), self.operands[1].__str__(atoms_res), self.operands[2].__str__(atoms_res))

    def smt_lib(self, atoms_res: list[str]) -> str:
        return "(ite {} {} {})".format(self.operands[0].smt_lib(atoms_res), self.operands[1].smt_lib(atoms_res), self.operands[2].smt_lib(atoms_res))

    def evaluate(self, atoms_res: list[bool]) -> bool:
        return self.operands[1].evaluate(atoms_res) if self.operands[0].evaluate(atoms_res) else self.operands[2].evaluate(atoms_res)
