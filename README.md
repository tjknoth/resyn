# Resyn #

Resyn synthesizes programs from _liquid resource types_ (ICFP '20), according to 
an upper bound on the programs' resource usage. 

For example, given the following type as the specification:
```
replicate :: n:Nat -> x:{a| |n} -[1]-> {List a | len _v = n}
```
and an appropriate set of components, Resyn will automatically generate a program: 
```
replicate = \n . \x . 
  if n <= 0
    then Nil
    else Cons x (replicate (dec n) x)
```

Resyn's main contribution is a type-directed resource analysis
integrated into Synquid's _round-trip_ type checking framework for
synthesis. 
Then, to provide an upper bound on the program's resource
usage, one annotates base types with "potential": `x:{Int| |3}`. 
This type indicates that 
`x` carries 3 units of potential, which can be used to pay for operations
with nonzero cost. 
In this way, the analysis is parametric with respect
to resources. By annotating functions appropriately, one can define simple 
models of resource semantics, counting memory usage, execution steps, or 
any other resource.

## Cost models ##

Resyn's resource analysis is parameteric with respect to the actual resource in
question.
Users have two choices when specifying resource semantics. When type-checking,
the expression `tick c e` evaluates `e` while incurring (possibly negative) cost `c`.
To specify a simple cost model when _synthesizing_ functions, one can annotate function
arrows with a cost c: `foo :: a -[c]-> b`. 
This means that whenever the synthesizer guesses an application of `foo`, it
implicitly wraps it in a `tick c` expression.


## Resource annotations ##

One specifies resource bounds by annotating type signatures. 
Base types are annotated with "potential":
`{Int|_v >= 0 |3}` is the type of natural numbers carrying three
units of potential.
Potential is used to pay for operations with nonzero cost.
Potential can also be embedded in data structures -- the type
`List {Int| |1}` describes a list in which every element contains
one unit of potential.
To describe non-uniform distribution of resources (i.e. polynomial or
exponential bounds), one can use the technique described in our Liquid
Resource Types paper (citation coming soon!).
Finally, polymorphism implies resource polymorphism. 
One can instnatiate type variables with a potential-annotated type
in order to use functions in different contexts. 
Instantiating `List {a| |1}` with `a |-> {Int| |2}` yields
`List {Int| |3}`, for example.
One can use program expressions in resource annotations.

Details on the language and syntax can also be found in the wiki.


## Try Resyn ##
* [Resyn demo](http://comcom.csail.mit.edu/comcom/#ReSyn)
* [Liquid resource type checker demo](http://comcom.csail.mit.edu/comcom/#LRT)
* **Build from source:** You will need [stack](https://docs.haskellstack.org/en/stable/README/) and [z3](https://github.com/Z3Prover/z3) version 4.7.1. Clone this repository and then run ```stack setup && stack build``` from its top-level directory.  You can then run Resyn using ```stack exec -- resyn [args]```.

## Usage notes ##
* Resource analysis makes termination checking unnecessary (as long some
  operations actually consume resources), so to avoid proving termination (via a
  "termination metric", one can run Resyn with `-f Nonterminating`
* By default, Resyn is a "round-trip" type checker. This useful for detecting
  errors early when synthesizing, but less useful when using Resyn as a
  typechecker. The flag `--eac` will run Resyn in "enumerate" mode; waiting to
  solve resource constraints after processing the whole program. This will
  improve performance significantly when using Resyn as a typechecker (but
  degrade synthesis performance).
* When solving resource constraints with dependent annotations, one has a choice
  of three solvers. The incremental CEGIS solver currently has
  some bugs with constraints involving abstract potentials.
  One can also use [CVC4](https://cvc4.github.io/) as a (currently slow) backend. To do so, install a
  version of CVC4 released after 4/20/20, and set `--res-solver=cvc4`.

## Papers ## 
Technical details on the language and type system can be found in the research
papers:

[Resource-Guided Program Synthesis (PLDI '19)](https://arxiv.org/abs/1904.07415)


[Liquid Resource Types (ICFP '20)](https://arxiv.org/abs/2006.16233)
