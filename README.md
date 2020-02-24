# Resyn #

Resyn synthesizes programs from refinement types, according to 
an upper bound on the programs' resource usage. 

For example, given the following type as the specification:
```
#!haskell

replicate :: n:Nat -> x:{n**a| |n} -[1]-> {List a | len _v = n}
```
and an appropriate set of components, Resyn will automatically generate a program: 
```
#!haskell

replicate = \n . \x . 
  if n <= 0
    then Nil
    else Cons x (replicate (dec n) x)
```

Resyn's main contribution is a type-directed resource analysis
integrated into Synquid's _round-trip_ type checking framework for
synthesis. To describe resource semantics, one annotates function 
arrows with a cost c: `foo :: a -[c]-> b`. This means that evaluating 
`foo` has cost `c`. Then, to provide an upper bound on the program's resource
usage, one annotates types with "potential": `x:{Int| |3}`. This indicates that 
`x` carries 3 units of potential, which can be used to pay for operations
with nonzero cost. In this way, the analysis is parametric with respect
to resources. By annotating functions appropriately, one can define simple 
models of resource semantics, counting memory usage, execution steps, or 
any other resource. 

One can also annotate polymorphic types with multiplicities:
`x:{n ** a| |n}` essentially means that the synthesizer is allotted `n` copies 
of `x`. 
Potentials can range over natural numbers or program variables. 
Multiplicities can also range over natural numbers or program variables. 
The implementation allows using program variables as multiplicities, 
but it makes the problem undecidable in general.
Cost annotations can range over integers.


Resyn extends [Synquid](http://people.csail.mit.edu/polikarn/publications/pldi16.pdf)
with resource analysis in the tradition of [AARA](http://www.cs.cmu.edu/~janh/papers/aa_popl11.pdf)



## Try Resyn ##

* **Build from source:** You will need [stack](https://docs.haskellstack.org/en/stable/README/) and [z3](https://github.com/Z3Prover/z3) version 4.7.1. Clone this repository and then run ```stack setup && stack build``` from its top-level directory.  You can then run synquid using ```stack exec -- resyn [args]```.


