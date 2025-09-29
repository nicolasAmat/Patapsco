
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
from components import BinaryRepr, Entry, Rows, Columns
from system import System

class Table:
    """ L* inspired data structure.
    """
    def __init__(self, store_row: bool) -> None:
        """ Initializer.
        """
        # Data structure for rows
        self.row_values:    Rows              = Rows()
        self.max_prefix_size: int = 0

        # Optional data structure for output a certificate
        self.store_row: bool                  = store_row
        self.row_repr: dict[Entry,BinaryRepr] = {}

        # Data structure for columns
        self.column_values: Columns = Columns()

    def __str__(self) -> str:
        """ Textual representation.
        """
        return "\n[Table: Rows]\n" + str(self.row_values) + "\n[Table: Row Representatives]\n" + '\n'.join( str(k) + "\n  |-> " + str(self.row_repr[k]) for k in self.row_repr.keys()) + "\n[Table: Column Values]\n" + str(self.column_values)

    def add_row(self, system: System, value: BinaryRepr, starting_point: Optional[Entry] = None) -> Entry:
        """ Add a new row in the table T.
        """
        derivative = system.compute_left_derivative(value, starting_point)
        self.max_prefix_size = max(self.max_prefix_size, value.size)
        
        self.row_values.add(derivative)
        if self.store_row :
            new_repr = value
            if not starting_point is None:
                new_repr = self.row_repr[starting_point].append(value)
            if derivative in self.row_repr.keys():
                new_repr = new_repr if new_repr.size < self.row_repr[derivative].size else self.row_repr[derivative]
            self.row_repr[derivative] = new_repr
        return derivative


    def add_column(self, system: System, value: BinaryRepr) -> Entry:
        """ Add a new column in the table T.
        """
        derivative = system.compute_right_derivative(value)
        self.column_values.add(derivative, value)
        return derivative
    
    def set_row_complete(self, row: Entry):
        """ Set a row as 'complete'.
        """
        self.row_values.deactivate(row)

    def is_complete(self) -> bool:
        """ Check if all the rows are set as 'complete'.
        """
        return (self.row_values.num_active_elements() == 0)
    
    def row_oracle(self):
        """ Return a random row
        """
        return self.row_values.random()
