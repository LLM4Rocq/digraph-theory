# digraph-theory

**Directed graphs and tournaments for the Rocq / MathComp ecosystem.**

A formal library for *directed* graph theory built on
[MathComp](https://github.com/math-comp/math-comp) and
[mathcomp-classical](https://github.com/math-comp/analysis), targeting
mathematicians (classical logic; no constructivity constraint). It is the
**directed companion to [coq-graph-theory](https://github.com/rocq-community/graph-theory)**:
the undirected clique / colouring / minor machinery is *reused* from there; this
library adds what is missing for digraphs and tournaments.

First concrete goal — **achieved**: a formalised infinite family of
`5`-`ω̄`-critical tournaments `ACₙ[ACₙ]`, proving
**Aboulker–Aubian–Charbit–Lopes Conjecture 5.10 at `k = 5`** and showing
**Question 5.9 fails at `k = 5`** (`applications/k5/main.v`, axiom-free). The
full design, module map, and milestone roadmap are in
**[`docs/DESIGN.md`](docs/DESIGN.md)**.

## Status

**Milestones M1–M3 — done (2026-06-11). The reusable directed/tournament
theory is complete (first public release point).**
M1: the HB hierarchy (`DiGraph` → `Tournament`), vertex orders as permutations
with the order-realization theorem, the backedge graph as a graph-theory
`sgraph`, and the tournament clique number `ω̄` (realized minimum, ω̄ = 1 ⟺
transitivity, monotonicity under embeddings / sub-tournaments / deletion,
iso-invariance); exit theorems `ω̄(C3) = 2`, `ω̄(TTₙ) = 1`, and C3 the *unique*
2-ω̄-critical tournament. M2: automorphism groups and vertex-transitivity, the
lexicographic substitution `S[H]` (tournament-closed), Cayley digraphs
(tournament iff `A ⊎ A⁻¹ = G∖{1}`; vertex-transitive via translations), and
circulants over `'Z_n` — the paper's `AC m` on `2m+1` vertices is a canonical,
vertex-transitive tournament. M3, the three marquee general theorems:
**substitution lower bound** `ω̄(S)+ω̄(H) ≤ ω̄(S[H])+1`, **vertex-transitive ⇒
uniform deletion** (criticality needs a single deletion), and **directed
domination** with `dom(T) ≤ ω̄(T)`. Everything axiom-free and cross-checked
against the exact Python oracle in [`scripts/`](scripts/). The target paper
lives in [`paper/`](paper/). Dev switch: opam switch `digraph` (Rocq 9.1.1 +
MathComp 2.5.0 + mathcomp-classical 1.16.0 + coq-graph-theory 0.9.7), linked
to this directory.

**M4 (the ACₙ base facts) — done (2026-06-11):** for every n = 2m+1 with
m ≥ 3, `ω̄(ACₙ) = 3` (bucket pigeonhole up; domination + the
interval-autocorrelation lemma down), `ω̄(ACₙ − v) = 2` for all v, and ACₙ is
**3-ω̄-critical** — paper Proposition "Facts about ACₙ", axiom-free,
oracle-checked on AC₇/AC₉.

**M5 (lower bounds for T = ACₙ[ACₙ]) — done (2026-06-11):**
`ω̄(T) ≥ 5` and `ω̄(T − (0,0)) ≥ 4`, both directly from the M3 substitution
theorem and the M4 values.

**M6 (upper bounds + assembly) — done (2026-06-11). The formalization of the
paper is complete.** Lemma H17 (`in_neighbourhood`), the 9-cell key order and
the cell Lemma (`cells`), the 20 infeasible cell-sets (`obstructions`), the
256-case coverage check (`coverage` — the one n-independent computational
step), giving `ω̄(T) ≤ 5` and `ω̄(T − (0,0)) ≤ 4` (`k5_upper`). `main.v`
assembles, for every odd `n = 2m+1 ≥ 7`: **`ω̄(ACₙ[ACₙ]) = 5`**,
**`ω̄(T − v) = 4` for every v** (by vertex-transitivity of the product, added
to `constructions/product.v`), **`T5_kcritical5`** (5-ω̄-critical, order
`n²`), **`conjecture_5_10_at_k5`** (the infinite family), and
**`question_5_9_fails_at_k5`** (every proper subtournament has `ω̄ ≤ 4`, so
no bound `ℓ(5)` exists). All exit theorems `Print Assumptions`-clean.

## What's here / coming

| Layer | Module(s) | Milestone |
|---|---|---|
| Foundations | `foundations/prelude` ✅, `foundations/interop_graph_theory` ✅ | M0–M1 |
| Core | `core/digraph` ✅, `core/tournament` ✅, `core/order` ✅ | M1 |
| Invariants | `invariants/omegabar` ✅, `…/critical` ✅, `…/domination` ✅, `…/dichromatic` | M1–M3 |
| Constructions | `constructions/{product,cayley,circulant,automorphism}` ✅ | M2 |
| General theorems | `substitution` ✅, `transitive` ✅ | M3 |
| Application | `applications/k5/{acn_arc_facts,acn_base,k5_lower,in_neighbourhood,cells,obstructions,coverage,k5_upper,main}` ✅ | M4–M6 |

## Build

Requires Rocq/Coq ≥ 8.19, MathComp ≥ 2.5.0, mathcomp-classical ≥ 1.16.0,
Hierarchy Builder ≥ 1.5.0. (From M1, also `coq-graph-theory` ≥ 0.9.7.)

```sh
# in an opam switch with the dependencies above
make            # builds everything listed in _CoqProject
make clean
```

The build delegates to a `Makefile.coq` generated from `_CoqProject` via
`coq_makefile` / `rocq makefile` — the standard rocq-community pattern. `coqc`
finds the MathComp dependencies automatically (opam `user-contrib`).

## Installing dependencies (example)

```sh
opam switch create . --packages=rocq-prover.9.1.1     # or reuse an existing switch
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-mathcomp-ssreflect rocq-mathcomp-algebra \
             rocq-mathcomp-fingroup rocq-mathcomp-classical rocq-hierarchy-builder
# from M1:
opam install coq-graph-theory
```

## Conventions

- File names are lowercase (`tournament.v`, `omegabar.v`), matching MathComp and
  graph-theory; structure identifiers keep the usual MathComp casing.
- Lower layers never depend on higher ones; `coq-graph-theory` is imported in
  exactly one file (`foundations/interop_graph_theory.v`).
- See [`CONTRIBUTING.md`](CONTRIBUTING.md) and [`docs/DESIGN.md`](docs/DESIGN.md).

## License

Apache-2.0 — see [`LICENSE`](LICENSE).
