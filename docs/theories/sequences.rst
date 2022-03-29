Theory Reference: Sequences
===========================

.. note::
  cvc5 currently only supports sequences where the element sort either has an
  infinite domain, e.g., sequences of integers, or a finite domain of a fixed
  cardinality, e.g. bit-vectors.

Semantics
^^^^^^^^^

.. code-block::

  * (seq.empty (Seq S))

    ⟦seq.empty⟧ = []

  * (seq.unit S (Seq S))

    ⟦seq.unit⟧(x) = [x]

  * (seq.len (Seq S) Int)

    ⟦seq.len⟧(s) is the number of elements in the sequence s, denoted as |s|

Syntax
^^^^^^

For the C++ API examples in the table below, we assume that we have created
a ``cvc5::api::Solver solver`` object.

+----------------------+----------------------------------------------+--------------------------------------------------------------------+
|                      | SMT-LIB language                             | C++ API                                                            |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Logic String         | use `S` for sequences and strings            | use `S` for sequences and strings                                  |
|                      |                                              |                                                                    |
|                      | ``(set-logic QF_SLIA)``                      | ``solver.setLogic("QF_SLIA");``                                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sort                 | ``(Seq <Sort>)``                             | ``solver.mkSequenceSort(<Sort>);``                                 |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Constants            | ``(declare-const X (Seq Int))``              | ``Sort s = solver.mkSequenceSort(solver.getIntegerSort());``       |
|                      |                                              |                                                                    |
|                      |                                              | ``Term X = solver.mkConst(s, "X");``                               |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Empty sequence       | ``(as seq.empty (Seq Int))``                 | ``Sort intSort = solver.getIntegerSort();``                        |
|                      |                                              |                                                                    |
|                      |                                              | ``Term t = solver.mkEmptySequence(intSort);``                      |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Unit sequence        | ``(seq.unit 1)``                             | ``Term t = solver.mkTerm(Kind::SEQ_UNIT, solver.mkInteger(1));``   |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Sequence length      | ``(seq.len X)``                              | ``Term t = solver.mkTerm(Kind::SEQ_LENGTH, X);``                   |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
