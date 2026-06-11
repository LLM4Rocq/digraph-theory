(** * Digraph.prelude — shared foundations

    Common imports, global options, and a classical-logic baseline for the whole
    library. Every other file should [From Digraph Require Import prelude.] first.

    Design (see docs/DESIGN.md §2): we work classically (mathcomp-classical's
    [boolp]) so statements read like ordinary mathematics — excluded middle,
    propositional and functional extensionality, and choice are available. The
    [classical_sets] layer ([set T] over an arbitrary [T]) is the seam through
    which the finite, combinatorial core will later extend to infinite / arbitrary
    vertex types (Decision D4). The finite workhorse types come from MathComp
    proper ([finType], [{set T}], [{perm T}], ['Z_n], ...). *)

From mathcomp Require Import all_boot.
From mathcomp Require Import boolp classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

(** ** Smoke checks

    These exercise both layers so a broken toolchain fails fast at [make] time.
    They carry no mathematical content and may be removed once real modules land. *)

(** Classical logic is in scope (derived from [boolp]'s axioms). *)
Lemma prelude_classical (P : Prop) : P \/ ~ P.
Proof. by case: (pselect P); [left | right]. Qed.

(** The classical set layer is in scope. *)
Lemma prelude_set (T : Type) (A : set T) : A `<=` setT.
Proof. by move=> x _. Qed.

(** MathComp's small-scale reflection is in scope. *)
Lemma prelude_ssr (n : nat) : (n <= n)%N.
Proof. by []. Qed.
