# 🧮 Patapsco — *Presburger Arithmetic To Automata Prober of State COmplexity*

[![License](https://img.shields.io/badge/license-GPLv3-blue.svg)](LICENSE)


---
Presburger arithmetic is the first-order theory of the natural numbers with **addition** and **order**. A Presburger formula can be represented as a **deterministic finite automaton (DFA)** whose accepted language corresponds to its solutions.

Given an input formula in [**SMT-LIB format**](https://smt-lib.org/), Patapsco computes **certified lower bounds** on the number of states required by the corresponding minimal DFA.

---

## ✨ Features

- Computes **lower bounds** on the number of states for encoding an input formula ([SMT-LIB](https://smt-lib.org/) format).
- Generates and verifies **certificates**.
- **Combine** different certificates obtained for a same input formula.

---

## 🧩 Dependencies

Before running Patapsco, ensure the following dependencies are installed:

- [**PySMT**](https://pypi.org/project/PySMT/)
- [**Z3 Theorem Prover**](https://github.com/Z3Prover/z3)

Install dependencies using pip:

```bash
pip3 install pysmt z3-solver
```

---

## 🚀 Usage

Run the tool with:
```bash
./patasco.py -f <path_to_file.smt2>
```

Available options:
```
-h, --help            show the help message and exit

--version             Show the version number and exit

-v, --verbose         Increase output verbosity

-o OUTPUT, --output OUTPUT
                    Write a certificate in output. If the argument is a dot, the output is named "x.table", where "x" is the name of the input file

-c CERTIFICATE [CERTIFICATE ...], --certificate CERTIFICATE [CERTIFICATE ...]
                    Read one or more certificates. You can write a dot as an argument to check a certificate named "x.table", where "x" is the name of the input file

--check               Check the certificates. When providing this flag, the flags -o and --resume are ignored. This is the default behaviour when -f and -c are provided, but not -o nor --resume

--resume              Resume computation from the given certificates. This flag is ignored if --check is enabled. This is also the default behaviour when both -c and -o are given (but not --check). If -o is missing, no output certificate is produced

-d, --debug           Print the SMT-LIB input/output

-t TIME_LIMIT, --time-limit TIME_LIMIT
                    Time limit for the computation done with Z3

--suffixes            Close columns of the table under suffixes. This may indirectly increase also the number of prefixes. Using this together with the option --concrete may slow down Z3 significantly.

--signs               Add sign vectors to columns. This flag is ignored if --suffixes is enabled.

--concrete            Use concrete suffixes when when calling Z3. Enable this option when coefficients in the system are large, or if you anticipate large solutions/suffixes (these may slow down Z3 significantly).

--seed SEED           Set the random seed

-r RESET_PIVOT, --reset-pivot RESET_PIVOT
                      Advice the program on how many solutions should we search for a selected pivot

--stats               Prints statistics on the instance.

--only-stats          Prints statistics on the instance and exists.
```

---

## 🏆 Challenge

Help us for computing certified lower bounds!

Visit our [**challenge page**](https://patapsco.software.imdea.org/) to explore our **best known lower bounds** for `QF_LIA` formulas from the **SMT-LIB** repository.  

You can **contribute** by submitting improved certificates and pushing the limits further.

---

## 📚 Reference

> **Nicolas Amat, Pierre Ganty, Alessio Mansutti.**  
> *How Big is the Automaton? Certified Lower Bounds on the Size of Presburger DFAs.*  
> *ASE 2025.*  
> [https://patapsco.software.imdea.org/paper.pdf](https://patapsco.software.imdea.org/paper.pdf)


---

## 🧑‍💻 Authors

- Nicolas Amat  
- Pierre Ganty  
- Alessio Mansutti

---

## 📄 License

This project is licensed under the **GPLv3** — see the [LICENSE](LICENSE) file for details.