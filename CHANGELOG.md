# Changelog

All notable changes to this project are documented here.
The format loosely follows [Keep a Changelog](https://keepachangelog.com/).

## [Unreleased]

### Added — M6 (upper bounds + assembly: the k = 5 theorem), 2026-06-11
- `applications/k5/in_neighbourhood.v` — **Lemma H17**: for x in the Hi band
  and y in the Lo band, the common in-neighbourhood N⁻(x) ∩ N⁻(y) lies in a
  single band, the side determined by whether val x ≤ val y + m
  (`H17_side`); consumed as `H17_no_mixed` (no Hi/Lo pair of common
  in-neighbours) by the square obstructions.
- `applications/k5/cells.v` — bands (`band`, Hi/Lo/zero), the 9 cells
  (`cidx`), the radix-(9,n,n) **key order** `qk` (a genuine `{perm T5}` via
  the M1 realization theorem) and, for any clique K of its backedge graph:
  beats go down in key order (`beat_key`), **block-beat** and inner-beat
  decompositions (`beat_blocks`, `beat_inner`), the **cell Lemma**
  (`cidx_inj_clique`: at most one clique vertex per cell) and the occupancy
  count `card_clique_cidx : #|K| = Σ_(i<9) occ i`.
- `applications/k5/obstructions.v` — the **20 infeasible cell-sets** of
  paper §5.4(a) — ten triples, four outer-source quadruples, six squares —
  each refuted from the M4 arc-facts + H17 (`triple_A/B`, `quad_A/…/D`,
  `square`), packaged as `no_obstruction : obstrb (occ 0) … (occ 7) = false`.
- `applications/k5/coverage.v` — §5.4(b): any occupancy pattern avoiding all
  20 obstructions covers ≤ 4 of the 8 proper cells (`coverage5`) — the one
  n-independent computational step (256-case boolean `case` analysis, D6).
- `applications/k5/k5_upper.v` — assembly of the casework:
  **`omegabar_T_le5` : ω̄(T) ≤ 5** (cells 0–7 carry ≤ 4 clique vertices,
  cell 8 = {(0,0)} carries ≤ 1) and **`omegabar_Tdel_le4` : ω̄(T−(0,0)) ≤ 4**
  (key order pulled back along `val`; cliques avoid cell 8 entirely).
- `constructions/product.v` — added `lexprod_vertex_transitive`:
  vertex-transitivity is preserved by lexicographic product.
- `applications/k5/main.v` — **the theorem.** For every n = 2m+1, m ≥ 3:
  * **`omegabar_T5` : ω̄(ACₙ[ACₙ]) = 5**;
  * **`omegabar_T5_del` : ω̄(T − v) = 4 for every v** (vertex-transitivity
    of the product spreads the (0,0) bound);
  * **`T5_kcritical5` : ACₙ[ACₙ] is 5-ω̄-critical**; `card_T5 : #|T| = n²`;
  * **`conjecture_5_10_at_k5`** : for every N there is a 5-ω̄-critical
    tournament on > N vertices — Conjecture 5.10 of
    Aboulker–Aubian–Charbit–Lopes at k = 5;
  * **`proper_sub_omegabar_le4`** : every proper subtournament of T has
    ω̄ ≤ 4, hence **`question_5_9_fails_at_k5`** : no bound ℓ(5) exists —
    Question 5.9 fails at k = 5.
- All 9 exit theorems verified axiom-free (`Print Assumptions`: closed under
  the global context). **The formalization of the paper is complete.**

### Added — M5 (lower bounds for T = ACₙ[ACₙ]), 2026-06-11
- `applications/k5/k5_lower.v` — for n = 2m+1, m ≥ 3:
  * **`omegabar_T_ge5` : ω̄(ACₙ[ACₙ]) ≥ 5** — the M3 substitution lower
    bound instantiated with ω̄(ACₙ) = 3 (M4): 3 + 3 − 1.
  * **`omegabar_Tdel_ge4` : ω̄(T − (0,0)) ≥ 4** — (ACₙ−0)[ACₙ] embeds
    arc-preservingly into T − (0,0) (first-component `val` injection), and
    ω̄((ACₙ−0)[ACₙ]) ≥ 2 + 3 − 1 = 4 by the substitution bound again;
    conclude by `omegabar_embed`.
- Both axiom-free. (The matching upper bounds, completing ω̄(T) = 5 and the
  5-criticality, are the M6 casework.)

### Added — M4 (the ACₙ base facts), 2026-06-11
- `applications/k5/acn_arc_facts.v` — the value-arithmetic kit for 'Z_n
  (`val_sub_le`/`val_sub_gt`/`val_oppE`), connection-set membership by value,
  the **gap characterizations** of forward/backward arcs under the value
  order (`AC_arc_lt`, `AC_arc_gt`), the within-band arc rule (`AC_band_arc`)
  and the paper's band facts (i)–(ii) (`AC_mem_Hi(_opp)`, `AC_mem_Lo(_opp)`).
- `applications/k5/acn_base.v` — paper Proposition "Facts about ACₙ" for
  m ≥ 3:
  * **`omegabar_AC` : ω̄(ACₙ) = 3** — upper bound by the bucket pigeonhole
    (`bucket_bound`: backedges of the value order span gaps ≥ m, so cliques
    inject into 3 value-buckets); lower bound via `domnum_le_omegabar` with
    `cardN0` (#|N₀| = m+1 from the ±-partition), the shift algebra, and the
    **interval-autocorrelation lemma** (`autocorr_lo`/`autocorr2`:
    |N₀ ∩ (N₀+t)| ≥ 2 for t ≠ 0), giving **`domnum_AC_ge3`**.
  * **`omegabar_AC_del` : ω̄(ACₙ − v) = 2** for every v (2-bucket bound on
    the deleted vertex set; the triangle 1 → 2 → m+3 → 1 survives in
    ACₙ − 0; uniform over v by vertex-transitivity).
  * **`AC_kcritical3`** : ACₙ is 3-ω̄-critical (via `vt_kcritical`).
  (The "unique backedge triangle {0,m,2m}" clause of the paper's (a) is not
  formalized separately: criticality is obtained directly by the 2-bucket
  argument, which subsumes its only use.)
- All M4 theorems axiom-free; values oracle-checked (ω̄(AC₇)=ω̄(AC₉)=3,
  dom=3, ω̄(−0)=2).

### Added — M3 (general invariants — the marquee theorems), 2026-06-11
- `invariants_advanced/transitive.v` — **vertex-transitive ⇒ uniform
  deletion**: an automorphism restricts to an isomorphism of vertex-deleted
  sub-tournaments (`del_aut_iso`), so ω̄(T − v) is independent of v
  (`omegabar_del_vt`) and k-ω̄-criticality reduces to a single deletion
  (`vt_kcritical`). Demo: `AC_del_uniform`.
- `invariants/domination.v` — directed domination (`dominatesb`, `domnum`)
  and **Property 3.2: `domnum T <= ω̄(T)`** (`domnum_le_omegabar`), via the
  greedy ≺ₚ-minimum chain which is simultaneously dominating and a backedge
  clique (`greedy_clique_dom`). Oracle-checked tight on C3 (2 = 2) and TT₅
  (1 = 1).
- `invariants_advanced/substitution.v` — the **substitution lower bound**
  `ω̄(S) + ω̄(H) <= ω̄(S[H]) + 1` (`omegabar_lexprod_ge`, subtraction-free
  form of ω̄(S[H]) ≥ ω̄(S)+ω̄(H)−1): block-min representatives + promotion of
  the ≺-last block of a maximum block-clique, with the edge correspondences
  `cross_edgeE`/`block_edgeE`. Oracle-checked tight: ω̄(AC₃[AC₃]) = 3 =
  2+2−1.
- All M3 theorems axiom-free. **The reusable directed/tournament theory
  (M0–M3) is now complete — the natural first public release point.**

### Added — M2 (constructions), 2026-06-11
- `constructions/automorphism.v` — automorphisms as a group of permutations
  (`autb`, `dgaut` with canonical `{group {perm D}}` structure) and the
  `vertex_transitiveb` predicate.
- `constructions/product.v` — lexicographic substitution S[H] (`lexprod`):
  arcs by the outer tournament, ties broken by the inner one; canonical
  digraph instance on `S * H`, **tournament closure** (M2 exit), arc
  characterization, cardinality.
- `constructions/cayley.v` — Cayley digraphs `cayley A` over a finite group:
  arc `x --> y` iff `x^-1 * y ∈ A`; tournament characterization
  (`cayley_irreflP`, `cayley_totalP`: tournament iff `A ⊎ A^-1 = G \ {1}`);
  **left translations are automorphisms** and Cayley digraphs are
  **vertex-transitive** (M2 exit).
- `constructions/circulant.v` — 'Z_n's canonical group is the additive one
  (definitional bridges `Zp_mulgE`/`Zp_invgE`/`Zp_1gE`), so circulants are
  Cayley digraphs (`circulant_arcE : x --> y iff y - x ∈ A`). The paper's
  **ACₙ** (n = 2m+1, connection set {1,…,m−1} ∪ {m+1}) is a canonical
  **tournament** (`ACset_cond` — the residue-arithmetic heart — M2 exit),
  vertex-transitive, on 2m+1 vertices.
- All M2 theorems axiom-free; definitions cross-checked against the Python
  oracle (`AC(n, ac_gen(n))` is a tournament for n = 3,5,7; ω̄(AC₇) = 3;
  lex-substitution closure).

### Added — M1 (core + ω̄), 2026-06-11
- `foundations/interop_graph_theory.v` **activated**: exports graph-theory's
  `sgraph`/`clique`/`ω`/`α`/`χ` vocabulary + generic ω lemmas
  (`omega_ge1`, `omega_le1`, `omega_ge2`, `omega_le_card`, `omega_hom`) and the
  `omega_K2` smoke check. `coq-graph-theory` is now a hard dependency (D1).
- `core/digraph.v` — own HB hierarchy (D7): `HasArc` mixin, `RelDigraph`,
  `DiGraph` (`diGraphType`), `-->` notation, projection `to_GT` into
  graph-theory's record, `converse` alias, canonical sub-digraph instances on
  subtypes `{x | P x}`, `induced_digraph`/`del_vertex`, isomorphism `dgiso`.
- `core/tournament.v` — `Tournament` HB structure (irreflexive + totality as a
  boolean xor equation), arc calculus (`arc_asym`, `arcNarc`, …),
  neighbourhoods `N_out`/`N_in`, decidable transitivity `transb`, the 3-cycle
  dichotomy (`ntransbP`), `card_le2_transb`; sub-tournaments on subtypes;
  examples `C3` (directed triangle) and `TT n` (transitive tournament).
- `core/order.v` — vertex orders as `{perm V}` (`ltp`, D5 pinned), the
  **realization theorem** (`realize`, `ltp_realizeE`: every strict total order
  is `ltp` of a permutation) with `ltp_pullback` along injections; the
  **backedge graph** `backedge T p : sgraph`.
- `invariants/omegabar.v` — **ω̄** via `arg min` over `{perm T}`
  (`omegabar`, notation `ω̄(T)`); realized-minimum lemmas; `omegabar_transb`
  (ω̄ = 1 ⟺ transitive); monotonicity under arc-preserving embeddings
  (`omegabar_embed`), iso-invariance, sub-tournaments and deletion;
  **`omegabar_TT`: ω̄(TTₙ) = 1** and **`omegabar_C3`: ω̄(C3) = 2**
  (cross-checked against `scripts/core.py`).
- `invariants/critical.v` — `kcritical k T`; `card_del`;
  **`C3_kcritical2`** (C3 is 2-ω̄-critical), **`kcritical2_card3`** (any
  2-critical tournament has 3 vertices) and **`kcritical2_uniq`** (it is
  isomorphic to C3) — the M1 exit theorems.
- All M1 theorems are axiom-free (`Print Assumptions`: closed under the global
  context).

### Added
- **M0 scaffold.** Build system (`_CoqProject` + delegating `Makefile`), opam
  packaging (`rocq-`/`coq-digraph-theory.opam`), GitHub Actions CI, and project
  docs.
- `foundations/prelude.v` — classical baseline (mathcomp-classical) + MathComp
  imports; compiles against Rocq 9.1 / MathComp 2.5 / classical 1.16.
- `foundations/interop_graph_theory.v` — stub for the single bridge to
  coq-graph-theory (activated at M1).
- `docs/DESIGN.md` — full design, module map, and milestone roadmap.
