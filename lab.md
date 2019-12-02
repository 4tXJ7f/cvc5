# SMT Solver Lab

In this lab, we are implementing simple theory solvers for integer difference
logic (IDL) and uninterpreted functions (UF) in CVC4. CVC4 is a
state-of-the-art SMT solver and the goal of this lab is to give a taste of what
it takes to implement new theories in an SMT solver. The individual steps of
this lab build on each other, so it is advisable to follow them in order.

## Getting the Source Code and Compiling CVC4

Use [Git](https://git-scm.com/) to clone this repository and use `git checkout --track origin/assignment3` to use the branch that corresponds to this assignment.

Before we get started, we have to compile CVC4. CVC4 can currently be compiled
on Linux and macOS. It can be cross-compiled for Windows but compilation on
Windows is not supported at this time. If you are using Windows, consider using
the [Windows Subsystem for Linux
(WSL)](https://docs.microsoft.com/en-us/windows/wsl/install-win10) or a Linux
VM. Depending on your machine, the initial compilation may take a while.

Before compiling CVC4, install the required dependencies as listed in
[INSTALL.md](INSTALL.md).

Afterwards, we can configure CVC4 and build it as follows:

```
./configure.sh debug --ubsan --asan --no-proofs
cd build
make -j<number of processes>
```

Configuring CVC4 with `--ubsan` and `--asan` enables the undefined behavior
UndefinedBehaviorSanitizer (UBSan) and the AddressSanitizer (ASan). The former
detects [undefined behavior](https://en.wikipedia.org/wiki/Undefined_behavior)
whereas the latter detects memory errors. Compiling the code with UBSan and
ASan incurs a performance penalty but when developping C++ code, it is strongly
recommended to enable them because they help uncover subtle problems and can
help with debugging efforts. `--no-proofs` disables support for proofs and
unsat cores because we do not need them for this lab.

## A Simple IDL Solver

In this part of the lab, you will implement a simple IDL solver that supports
model generation (i.e. produces values that satisfy the constraints for
satisfiable instances). Implementing the IDL solver consists of two steps: the
decision procedure and model generation.

### The Decision Procedure

The theory solver takes a set of theory literals of the form `(<= (- y x) n)`
(when the SAT solver decided the theory literal to be `true`) and `(not (<= (-
y x) n))` (when the SAT solver decided the theory literal to be `false`). Note
that the negated literals can be recast to be in the same form as the positive
ones. For the purpose of this lab, we are only considering cases where all the
theory literals have a value assigned (in CVC4, that's when a check is done at
"full effort"). The purpose of the theory solver is to decide whether a given
assignment to theory literals results in a conflict or not.

After compiling CVC4 as described in the previous section, you can try running
it on [lab/example_idl_rewritten.smt2](lab/example_idl_rewritten.smt2):

```
$ bin/cvc4 --use-theory=idl ../lab/example_idl_rewritten.smt2
...
Expected result unsat but got sat
...
```

The option `--use-theory=idl` tells CVC4 that we want to use the IDL solver
instead of the generic arithmetic solver. The error appears because the meta
information for the file says that the result should be `unsat` (`(set-info
:status unsat)`) but CVC4 computed that the result should be `sat`. We have to
implement a decision procedure to detect conflicts to fix this.

For IDL, a decision procedure can be implemented as follows: Given a set of
literals of the form `(<= (- y x) n)`, we can construct a graph where we have
one node for every integer constant and an edge with weight `n` from the node
corresponding to `x` to the node corresponding to `y`. Now, the assignment has
a conflict if and only if the graph contains a negative cycle.

**Task**: The skeleton code in
[src/theory/idl/theory_idl.cpp](src/theory/idl/theory_idl.cpp) constructs a
graph and stores it in `d_matrix`. Your task is to complete
`TheoryIdl::negativeCycle()` that returns `true` if the graph contains a
negative cycle and `false` otherwise.

After completing the previous task and making sure that CVC4 now solves
[lab/example_idl_rewritten.smt2](lab/example_idl_rewritten.smt2) and
[lab/example_idl_rewritten_sat.smt2](lab/example_idl_rewritten_sat.smt2), try
running it on [lab/example_idl.smt2](lab/example_idl.smt2). An assertion fails:

```
$ bin/cvc4 --use-theory=idl ../lab/example_idl.smt2
(error "Assertion failure.                                      
...
  atom.getKind() == kind::LEQ
...
")
```

Compare the assertions in [lab/example_idl.smt2](lab/example_idl.smt2) and
[lab/example_idl_rewritten.smt2](lab/example_idl_rewritten.smt2). The
assertions are equivalent but in the latter, all the assertions are of the form
`(<= (- y x) n)`. The SMT-LIB logic
[QF\_IDL](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_IDL) (quantifier-free
IDL problems) allows constraints of the form `(op (- y x) n)`, `(op (- y x) (-
n))`, and `(op y x)` where `op` is one of `<`, `<=`, `>`, `>=`, `=`, or
`distinct` and not only `(<= (- y x) n)`. We can automatically rewrite these
constraints to the latter form in the solver.

**Task**: Complete `TheoryIdl::ppRewrite()` to rewrite the IDL constraints to
the form that `TheoryIdl::processAssertion()` expects.

_Hint_: Compare the constraints in `lab/example.smt2` and
`lab/example_idl_rewritten.smt2` to get an idea of what the rewrites should
look like.

If you would like to test your solver with additional inputs, you can use the
[SMT-LIB benchmarks for
QF_IDL](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_IDL).

### Model Generation

If you run CVC4 on
[lab/example_idl_rewritten_sat.smt2](lab/example_idl_rewritten_sat.smt2), you
may have noticed that CVC4 reports a model but the model is wrong (all the
values are zero):

```
$ bin/cvc4 --use-theory=idl ../lab/example_rewritten_sat.smt2
sat
(model
(define-fun x () Int 0)
(define-fun y () Int 0)
(define-fun z () Int 0)
(define-fun w () Int 0)
)
```

For IDL, a model can be generated by running a single-source shortest paths
algorithm. Conceptually, we add a node to our graph that has edges with weight
0 to all the other nodes and then compute the shortest path from that node to
all the other nodes. The distance of a node becomes its value in the model.

**Task**: Your task for this part of the lab is to complete
`TheoryIdl::collectModelInfo()` by computing the values in the `distance`
vector. The skeleton takes those `distance` values and asserts that the values
of the variables are the same as their distance.

## Optional: A Simple UF Solver

In this (optional) part of the lab, you will implement a simple UF solver. In
an additional step, we will investigate the challenges of combining that solver
with bit-vectors.

### The Decision Procedure

The UF solver receives as an input a list of equalities between terms (i.e. `(=
t1 t2)`) and disequalities between terms (i.e. `(not (= t1 t2))`). The terms
may contain applications of uninterpreted functions (i.e. functions that we
know nothing about except that they behave like functions). For simplicity, you
may assume that functions only take a single argument. For a concrete example,
take a look at [lab/example_uf.smt2](lab/example_uf.smt2). If we run CVC4 on
that example, the output is again wrong and you will implement a decision
procedure to fix this:

```
$ bin/cvc4 ../lab/example_ufbv.smt2
...
Expected result unsat but got sat
...
```

The decision procedure again computes whether there are conflicts between those
terms. To do this, we will use _congruence closure_. This algorithm computes
equivalence classes, which are sets of terms that are equivalent, and then uses
them to detect conflicts with the asserted disequalities:

1. For all `(= t1 t2)`, create a new equivalence class `{ t1, t2 }`. For all
   `(not (= t1 t2))`, create two new equivalence classes `{ t1 }` and `{ t2 }`.
2. Find two equivalence classes with a shared term and merge them. E.g. if we
   have the equivalence classes `{ t1, t2, t3}`, `{ t2, t4 }`, and `{ t5 }`, we
   can merge the first two classes and get `{ t1, t2, t3, t4 }`. Repeat until
   no two equivalence classes share a term.
3. If we have an equivalence class with two terms `t_i` and `t_j` and two terms
   `(f t_i)` and `(f t_j)` that are in the equivalence classes `eqc_i` and
   `eqc_j`, respectively, with `i != j` then we can merge `eqc_i` and `eqc_j`.
   Repeat until this rule doesn't apply anymore.
4. For each disequality `(not (= t1 t2))`, check if `t1` and `t2` are in the
   same equivalence class. If they are, there is a conflict.

**Task**: Implement the congruence closure algorithm in `TheoryUF::check()` in
[src/theory/uf/theory_uf.cpp](src/theory/uf/theory_uf.cpp).

If you would like to test your solver with additional inputs, you can use the
[SMT-LIB benchmarks for
QF_UF](https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_UF).

### Theory-Combination with Bit-Vectors

If you run CVC4 on [lab/example_ufbv.smt2](lab/example_ufbv.smt2), you may
notice that CVC4 reports that it computed an unexpected result:

```
$ bin/cvc4 ../lab/example_ufbv.smt2
...
Expected result unsat but got sat
...
```

This is because the meta information for the file says that the result should
be `unsat` (`(set-info :status unsat)`). Let's open the file and take a closer
look at the constraints:

```
(declare-sort U 0)
(declare-const x (_ BitVec 1))
(declare-const y (_ BitVec 1))
(declare-const z (_ BitVec 1))
(declare-fun f ((_ BitVec 1)) U)
(assert (not (= (f x) (f y))))
(assert (not (= (f y) (f z))))
(assert (not (= (f x) (f z))))
```

First, we declare an uninterpreted sort `U`. Then, we declare three bit-vector
constants `x`, `y`, and `z` of bit-width 1 (so essentially just Booleans).
Next, we declare a function `f` that takes a bit-vector of bit-width 1 and
returns a value of sort `U`. Finally, we have the actual assertions that say
that if we apply the function `f` to the bit-vector constants, we expect a
different result for each one of them. At first sight, this may seem
satisfiable and in fact it would be if the bit-vector sort did not have
cardinality 1. Because we have only two possible values for bit-vectors of
bit-width 1, applying `f` to the bit-vector constants cannot produce three
different values. This is also the reason why the Nelson-Oppen theory
combination does not work with bit-vectors: the theory of bit-vectors is not
stably-infinite. In CVC4, this problem is solved by making sure that we do not
need more representatives in the model than a given bit-vector sort admits
before answering that a problem is satisfiable.

**Task**: Your task is to generate a theory lemma in the bit-vector solver
whenever we detect that we would need to many representatives in a given model.
To do this modify the skeleton for `CoreSolver::buildModel()` provided in
[src/theory/bv/bv_subtheory_core.cpp](src/theory/bv/bv_subtheory_core.cpp). The
vector `representatives` holds a list of representatives and the goal is to
generate a list of `equalities` of the form `(= r_i r_j)`. The skeleton then
uses these equalities to generate a theory lemma of the form `(or (= r_0 r_1)
...)`, which signals that some of the representatives (and thus their
respective equivalence classes) have to be equal.
