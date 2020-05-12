# `syrup_backend`

This is a prototype implementation of the backend of the `syrup` tool
  chain presented in

> "Synthesis of Super-Optimized Smart Contracts using Max-SMT", CAV
> 2020, [Elvira Albert](https://costa.fdi.ucm.es/~elvira/), [Pablo
> Gordillo](https://costa.fdi.ucm.es/~pabgordi/), [Albert
> Rubio](https://costa.fdi.ucm.es/~arubio/), and [Maria A
> Schett](http://maria-a-schett.net/)

The tool takes as input a Stack Functional Specification (SFS)
describing the source and target stack of the Ethereum Virtual Machine
(EVM) and, if successful, produces synthesized and optimized EVM
bytecode to transform the source into the target stack by encoding the
problem into Max-SMT.

## Examples

In [`examples/add/input.json`](examples/add/input.json) is the SFS for
* source_stack: `[x_0, x_1, x_2, x3]`
* target_stack: `[x_0 + x1, x2 + x3]`

For this SFS `syrup_backend` produces the EVM bytecode:

```ADD SWAP2 ADD SWAP1.```

In [`examples/cav2020/input.json`](examples/cav2020/input.json) is the SFS for
* source_stack: `[]`
* target_stack: `[]`

For this SFS `syrup_backend` produces the EVM bytecode:

```.```

## Install & Run

The easiest way to install `syrup_backend` is using
[opam](https://opam.ocaml.org/).  Simply run `opam install .` after
cloning the repository. Then `syrup-backend -help` will provide help.

Max-SMT solvers supported by `syrup_backend` are
* [Z3](https://github.com/Z3Prover/z3), version4.8.7
* [Barcelogic](https://www.cs.upc.edu/~oliveras/bclt-main.html)
* [OptiMathSat](http://optimathsat.disi.unitn.it/), version 1.6.3

For each of these solvers, `syrup_backend` can `-write-only` an SMT
encoding. When given a `-path` to the executable of the respective
solver, `syrup_backend` calls the solver directly.

