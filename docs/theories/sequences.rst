Theory Reference: Sequences
===========================

.. note::
  cvc5 currently only supports sequences where the element sort has an infinite
  domain, e.g., sequences of integers.

Semantics
^^^^^^^^^

.. code-block::

  * (str.update (Seq S) Int (Seq S))

    - ⟦str.replace_re⟧(w, L, w₂) = u₁w₂⟦str.replace_re⟧(u₂, L, w₂)
      where u₁, w₁ are the shortest words such that 
            - w = u₁w₁u₂
            - w₁ ∈ L
            - w₁ ≠ ε
                                          if some substring of w is in L

    - ⟦str.update⟧(s₁, i, s₂) = s₁        if i < 0 or i >= |s₁|

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
| Intersection         | ``(setminus X Y)``                           | ``Term t = solver.mkTerm(Kind::SETMINUS, X, Y);``                  |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Membership           | ``(member x X)``                             | ``Term x = solver.mkConst(solver.getIntegerSort(), "x");``         |
|                      |                                              |                                                                    |
|                      |                                              | ``Term t = solver.mkTerm(Kind::MEMBER, x, X);``                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Subset               | ``(subset X Y)``                             | ``Term t = solver.mkTerm(Kind::SUBSET, X, Y);``                    |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Cardinality          | ``(card X)``                                 | ``Term t = solver.mkTerm(Kind::CARD, X);``                         |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Insert / Finite Sets | ``(insert 1 2 3 (singleton 4))``             | ``Term one = solver.mkInteger(1);``                                |
|                      |                                              |                                                                    |
|                      |                                              | ``Term two = solver.mkInteger(2);``                                |
|                      |                                              |                                                                    |
|                      |                                              | ``Term three = solver.mkInteger(3);``                              |
|                      |                                              |                                                                    |
|                      |                                              | ``Term sgl = solver.mkTerm(Kind::SINGLETON, solver.mkInteger(4));``|
|                      |                                              |                                                                    |
|                      |                                              | ``Term t = solver.mkTerm(Kind::INSERT, {one, two, three, sgl});``  |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Complement           | ``(complement X)``                           | ``Term t = solver.mkTerm(Kind::COMPLEMENT, X);``                   |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
| Universe Set         | ``(as univset (Set Int))``                   | ``Term t = solver.mkUniverseSet(s);``                              |
+----------------------+----------------------------------------------+--------------------------------------------------------------------+
