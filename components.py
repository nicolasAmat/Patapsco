
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
import random as rndm

Entry = tuple[int]

class BinaryRepr:
    """ Binary representation of an integer vector.
    """
    def __init__(self, vec: Optional[list[int]] = None):
        """ Initializer.
        """
        self.size:        int       = max(map(abs, vec)).bit_length() if vec else 0
        self.vec:         Entry     = tuple(vec) if vec else ()

    def __hash__(self) -> int:
        """ Basic hashing function.
        """
        return hash((self.size, self.vec))
    
    def __eq__(self, other): 
        if isinstance(other, BinaryRepr):
            return self.size == other.size and self.vec == other.vec
        else:
            return False
        
    def __lt__(self, other):
        if isinstance(other, BinaryRepr):
            return self.size < other.size or (self.size == other.size and self.vec < other.vec)
        else:
            return False
    
    def __str__(self) -> str:
        """ Textual representation.
        """
        return '(' + str(self.size) + ',(' + ','.join(str(int(v)) for v in self.vec) + '))'

    def __len__(self) -> int:
        """ Length function.
        """
        return self.size
    
    def prefixes(self, n = None):
        if n == None:
            n = self.size + 1

        for i in range(min(n - 1, self.size), 0, -1):
            p = BinaryRepr()
            p.size = i 
            p.vec = tuple((x if x >= 0 else 2**self.size + x) % (2**i) for x in self.vec)

            yield p
            
    def prefixes_and_suffixes(self):
        for i in range(self.size+1):
            p = BinaryRepr()
            p.size = i 
            p.vec = tuple((x if x >= 0 else 2**self.size + x) % (2**i) for x in self.vec)

            s = BinaryRepr()
            s.size = self.size-i
            s.vec = tuple(x // (2**i) for x in self.vec)

            yield (p,s)

    def sign_vector(self): 
        s = BinaryRepr() 
        s.size = 0 
        s.vec = tuple(x // (2**self.size) for x in self.vec)

        return s

    def append(self, b):
        if b.size == 0:
            return self
        elif self.size == 0:
            return b
        else: 
            p = BinaryRepr()
            p.size = self.size + b.size
            p.vec = tuple(self.vec[i] + (b.vec[i] << self.size) for i in range(len(self.vec)))
            return p

class Rows:
    """ Data structure for rows. 
        It stores active and completed rows (the latter first).
        It provides O(1) add, remove (deactivate), membership (had and contains) and get_random methods
    """

    def __init__(self):
        """ Initializer.
        """
        self.vec : list[Entry] = []
        self.hash_map : dict[Entry,int] = {}
        self.start = 0

    def __str__(self) -> str:
        return "** Row vectors:\n" + '\n'.join("("+ ','.join(str(int(e)) for e in v) + ")" for v in self.vec) + "\n** Hash Map:\n" + '\n'.join(('(' + ','.join(str(int(e)) for e in k) + ')') + "\n  |-> " + str(self.hash_map[k]) for k in self.hash_map.keys()) + "\n** Start: " + str(self.start)

    def add(self, e: Entry):
        if not (e in self.hash_map.keys()):
            self.hash_map[e] = len(self.vec)
            self.vec.append(e)

    def deactivate(self, e: Entry):
        i = self.hash_map.get(e)
        if i != None and i >= self.start:
            c = self.vec[self.start]
            self.vec[i] = c
            self.hash_map[c] = i
            self.vec[self.start] = e
            self.hash_map[e] = self.start 
            self.start = self.start + 1

    def had(self, e:Entry):
        return e in self.hash_map.keys()
        
    def contains(self, e: Entry):
        if e in self.hash_map.keys():
            return self.hash_map[e] >= self.start
    
    def random(self):
        i = rndm.randrange(len(self.vec)-self.start)
        return self.vec[self.start+i]
    
    def elements(self):
        return self.vec
    
    def num_elements(self):
        return len(self.vec)
    
    def num_active_elements(self):
        return len(self.vec) - self.start
    
    def num_inactive_elements(self):
        return self.start

class Columns: 
    """ Data structure for columns.
    """

    def __init__(self):
        """ Initializer.
        """
        self.column_suffixes: dict[Entry,set[BinaryRepr]] = {}

    def __str__(self) -> str:
        return '\n'.join((str(k) + "\n  -> set{ " + ','.join(str(b) for b in self.column_suffixes[k])) + "\n     }" for k in self.column_suffixes.keys())

    def add(self, e : Entry, b : BinaryRepr):
        if not (e in self.column_suffixes):
            self.column_suffixes[e] = set()
        self.column_suffixes[e].add(b)

    def get(self):
        return self.column_suffixes.keys() 
    
    def get_words(self, e: Entry):
        return self.column_suffixes.get(e)
    
    def num_elements(self):
        return len(self.get())
    
