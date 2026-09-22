# The Collatz bridge in Lean — implementation plan

Status: **PLAN, nothing built** (21 September 2026). No Lean has been written
for it, no ledger row has changed, no floor has moved. The state of the Lean
layer in Section 1 was read from the working tree on 21 September 2026 with
`tools/formalpedia.py` and direct reads of the sources; several sessions work
the tree at once, so re-run `impact` and `search` before acting on any line
of it.

Scope. The shortcut \(3x+1\) map rounds \(3n/2\) up on odd \(n\), the
\(3x-1\) map rounds it down, and the Juggler rounds \(n^{3/2}\) down, one
exponential level up. The three share one walk, the multipliers \(3/2\) and
\(1/2\), and one linear form \(o\log3-K\log2\). What is in Lean today states
that sharing at the word level and stops; what is missing is the join between
the two Lean copies of the \(3x-1\) map, a single statement of the sign flip,
and a kernel-checked sieve for the \(3x-1\) floor. The standing wall is
restated in Section 6 and nothing here crosses it: a shared word shape carries
no realization, so no item excludes a Juggler cycle or raises a floor.

```text
Mathematical target     make the bridge one machine-checked object: join the two
                        Lean copies of the 3x-1 map, state the sign flip once,
                        kernel-check the sieve the 2^51 floor uses
Novelty hypothesis      none at the word level; the join yields two theorems that
                        exist today only as halves on different objects (the
                        Lemma 8 window; Paper D Lemma 2's sign clause on negT),
                        and the sieve lemma raises the floor's method to kernel
Falsifier               a transported statement that needs a Juggler realization;
                        a barrel or trust rule broken; a duplicate definition
Already killed by?      none: J-word-density-results-are-not-juggler-specific and
                        J-juggler-cycle-words-are-collatz-negative-cycle-words
                        class every item as SHARED, and negative_knowledge.md has
                        no entry against a Lean join
Existing machinery      Problems.Juggler.CollatzBridge (integer shortcut map at
                        negative arguments), Problems.Collatz.NegativeMCycles
                        (negT), CycleFinance, IdealCycleMin, FateContagion;
                        Mathlib GenContFract, Real.logb
Maximum Phase-0 scope   Tier 1 (Section 2): one auxiliary module for the join and
                        its corollaries, one for the cocycle lemma, one Collatz-
                        side file for the negT sieve, four small completions
Promotion criterion     the window theorem and the sieve lemma compile kernel-only,
                        and the rows they cover move to EXACT — LEAN VERIFIED
                        after jev-coverage on each row alone
Stop criterion          an item that needs a Juggler realization hypothesis, or
                        Rhin's measure as a theorem rather than a hypothesis, or
                        native_decide inside Paper A's barrel
```

## 1. State of the Lean layer, verified 21 September 2026

**Two Lean objects for the \(3x-1\) map, unconnected.**

- `Problems.Collatz.NegativeMCycles` (`formal/Problems/Collatz/NegativeMCycles.lean`,
  24 declarations, kernel-only, imports Mathlib only, imported by
  `formal/Problems.lean` alone). Defines `negT` and `negTIter` on the naturals
  and proves Paper D's Lemmas 1 and 3: `negT_run_iter`, `negT_run_odd`,
  `negT_run_even`, `negT_start_ge` (a run of \(a\) odd steps starts at
  \(y\ge2^a+1\)), `negT_localMax`, `negT_lemma_one`, `negT_chain_nat`,
  `negT_chain_real`, `negT_lemma_three`, and the three cycles by `decide`.
  Lemma 2 (the cycle equation and \(\Lambda<m/(x_{\min}-1)\)), Lemma 5 (the
  sieve the floor uses) and Lemma 6 (the valley count) are human proofs.
- `Problems.Juggler.CollatzBridge` (81 declarations, a Paper A layer module,
  kernel-only, reached by `Problems.JugglerPaper`). Defines `shortcutZ`,
  `shortcutZIter`, `parityWordZ`, `evenCharge`, and proves `cycle_equation_int`,
  `neg_cycle_expanding`, `neg_prefix_noncontracting`,
  `neg_cycle_word_is_juggler_shape`, `two_mul_evenCharge_le`,
  `neg_cycle_finance`, the cycles `neg_one_cycle`, `neg_five_cycle`,
  `neg_seventeen_cycle`. Positive side: `shortcutC` (restated locally),
  `word_affine`, `parityWord_eq_iff`, `image_parityWord`,
  `undecidedResidues_card`, `le_iter_of_prefixNoncontracting`,
  `iter_lt_of_exponentGap_class`, `cycle_contracting`. Juggler side:
  `juggler_word_power`, `juggler_cycle_expanding`.
- Neither file names the other. Paper D (Section 3, Lemma 2) says the sign
  clause \(\Lambda>0\) is "the negative-cycle expansion already in Lean on the
  conjugate side". That conjugacy is a sentence in the manuscript, not a
  declaration.

**The sign flip is three separate proofs with no shared lemma.**
`cycle_contracting` on the naturals, `neg_cycle_expanding` on the integers,
and `juggler_cycle_expanding` (`cycle_itinerary_formally_expanding` in
`CycleCore`) with its real unroll `cycleMin_log_envelope` in `CycleFinance`.
`formal/Problems/Collatz/Cycles.lean` holds integer affine identities only
(`dvd_of_periodic_fixed_point`, `expanding_excludes_positive_candidate`,
`cycle_closure_of_affine_steps`).

**Paper C side.** `BackwardClosed`, `floorPower_even_block` (`FateContagion`),
`contagion_of_production_inequality`, `natDensity_averaged`,
`tao_rate_iff_conjecture`. No definition of the production coefficient
\(c_w\); the Collatz exhibit \(\{3\cdot2^k\}\) is not in Lean.

**Exponent dictionary.** The 2-adic half is in Lean (`Equality.lean`:
`isSquare_pow_three_iff`, `floorPower_of_pow_two_depth_even`,
`floorPower_of_pow_two_depth_odd`, `power_bound_eq_implies_pow_two_depth`).
The 3-adic half is in neither Lean nor the ledger. Checked by brute force
below 3000 on 21 September 2026: the exact even preimage \(m^2\) of \(m\)
exists iff \(m\) is even; the exact odd preimage \(s^2\) exists iff
\(m=s^3\) with \(s\) odd; 7 such targets below 3000, against 1000 residues
\(2 \bmod 3\) for the Collatz odd preimage \((2m-1)/3\).

**Ledger rows in this cluster with no Lean.** `J-cycle-gaps-are-mirror-images`,
`J-collatz-walk-charge-constant`, `J-paper-c-collatz-analogue-is-false-by-exhibit`,
`J-paper-c-ceiling-is-the-collatz-walk-mgf`,
`J-lemma-eight-floor-is-tight-at-every-known-cycle`,
`J-knight-is-sign-free-and-catalan-bounds-the-escapes`,
`J-even-run-dual-of-lemma-eight-is-capped-by-the-shape`,
`J-negative-m-cycle-lemmas` (names no Lean file although
`NegativeMCycles` proves Lemmas 1 and 3),
`J-kl-preimage-density-transposes-to-3n-1`.

**Mathlib, checked 21 September 2026 through leansearch.** No Catalan-type
lemma for \(3^x-2^k=\pm1\). Convergent alternation is available as
`GenContFract.sub_convs_eq`, which carries the sign \((-1)^n\).

**Architecture constraints that bind every item.** Paper A's barrel is
kernel-only and its layer modules import only `Problems.Juggler.*`
(`test_imports_are_one_way`); `CollatzBridge` restates `shortcutC` locally
because `Problems.Collatz.Shortcut` carries `native_decide` (`shortcutC_one`,
`shortcutC_two`). Every file in `formal/Problems/Juggler/` must be in
`LAYERS` or `AUXILIARY_MODULES` of `lean_paths.py`
(`test_every_juggler_source_has_an_explicit_inventory_role`). Declaration
names at most 33 characters (the Paper C axiom probe). The words `sorry`,
`admit`, `axiom` may not appear in a registered file, not even in comments.
Paper A Section 1.2 counts exactly one `native_decide` in the Juggler layer;
do not add a second.

## 2. Tier 1 — the join and the cheap completions

### 2.1 `CollatzBridgeNeg.lean` — the conjugacy

File `formal/Problems/Juggler/CollatzBridgeNeg.lean`, an auxiliary module.
Imports `Problems.Juggler.CollatzBridge` and `Problems.Collatz.NegativeMCycles`;
the second is kernel-only and Mathlib-only, so no trust rule breaks, and the
one-way import test polices layer modules only. Register in
`AUXILIARY_MODULES` and in `formal/Problems/Juggler.lean`; not in
`PAPER_MODULES`, not in `JugglerPaper.lean`.

Statements, in order:

1. `negT_eq_natAbs_shortcutZ`: for \(1\le y\),
   `negT y = Int.natAbs (shortcutZ (-y))`; the iterate form
   `negTIter k y = Int.natAbs (shortcutZIter k (-y))`; and the parity words
   agree (define a `negParityWord` for `negT` here if none exists, and prove
   it equal to `parityWordZ (-y)`). Prove the one-step identities in the
   style of `two_mul_shortcutZ` first; the only trap is integer division of
   \(-y\) at even steps against `y / 2`.
2. Transport: `negT_cycle_expanding` (a `negT` cycle at \(y\ge2\) has
   \(3^o>2^K\)), `negT_cycle_shape` (at its least element the word is
   `prefixNoncontracting` and expanding), `negT_cycle_finance`
   (\(2(y-1)(3^o-2^K)\le(K-o)\,3^o\)).
3. `negT_window`: on a `negT` cycle with least element \(y\), leading odd
   run \(a\) from `negT_lemma_one`, \(o\) odd letters and \(e=K-o\):
   \(2^a+1\le y\) and \(2(y-1)(3^o-2^K)\le e\,3^o\). This is the window of
   `J-lemma-eight-floor-is-tight-at-every-known-cycle`, today two halves on
   two objects.
4. `ooe_pins_five`: a `negT` cycle with word `OOE` has least element 5
   (the window is \([5,\,11/2]\)). `neg_seventeen_window`: the \(-17\) word
   gives \(17\le y\le32\) (\(a=4\), \(e=4\), \(3^7-2^{11}=139\),
   \(2\cdot16\cdot139=4448\le8748\)).
5. Paper D Lemma 2's sign clause is then `negT_cycle_expanding`; cite it in
   the manuscript's Section 3 in place of the sentence.

Buys: the two halves become one object; the window row and the sign clause
of `J-negative-m-cycle-lemmas` become Lean; Paper D's remark becomes a
citation. Size: days.

### 2.2 `RoundingCocycle.lean` — the sign flip once

An auxiliary module (or a Collatz-side file; it imports nothing from the
Juggler layer). Over an ordered field, for a list of steps with multipliers
\(c_i\in\{3/2,1/2\}\) and corrections \(\delta_i\), with
\(x_{i+1}=c_i x_i-\delta_i\):

- `cocycle_unroll`: \(x_K=(\prod c)\,x_0-\sum_i\delta_i\prod_{j>i}c_j\).
- `cycle_of_downward`: \(x_K=x_0>0\), all \(\delta_i\ge0\), \(K\ge1\)
  imply \(\prod c>1\), that is \(3^o>2^K\) (the equality case
  \(3^o=2^K\) is excluded by coprimality for \(K\ge1\)).
- `cycle_of_upward`: all \(\delta_i\le0\) imply \(3^o<2^K\).
- `charge_identity`:
  \(x_0(3^o-2^K)=\sum_i\delta_i\,3^{o_{>i}}\,2^{i+1}\).

Instances, each a short lemma: the integer shortcut map at negative
arguments with \(x_i=-(x_i+1)\) and \(\delta=1/2\) on even letters
(recovers `cycle_equation_int` divided by \(2^K\)); the positive shortcut
map with \(\delta=-1/2\); the Juggler with \(x_i=\log n_i\) and \(\delta_i\)
the floor loss (state through `Real.log` of `floorPower`;
`cycleMin_log_envelope` already bounds the same quantities); the ceiling
Juggler with \(\delta\le0\), through a local `ceilPower` that is not
exported. Keep the three existing sign theorems and their names; add the
cocycle proofs beside them or replace proofs only, never statements, since
`CollatzBridge` reaches `JugglerPaper`.

Buys: the bridge's central claim is one theorem with the sign as its only
parameter. Ledger label: REPARAMETERIZATION. Size: a day or two.

### 2.3 `NegativeSieve.lean` — Paper D Lemma 5

File `formal/Problems/Collatz/NegativeSieve.lean`, imported by
`formal/Problems.lean`; a separate file keeps the module Paper D cites fixed.
Statements for `negT`, each a sign mirror of a proof already in
`CollatzBridge.lean`:

- `negT_word_affine`: \(2^d\cdot\text{negT}^d(y)=3^o y-\text{negConst}\,w\)
  with \(\text{negConst}\,w\ge0\) a function of the word alone (mirror of
  `word_affine`; the constant is subtracted).
- `negT_parityWord_eq_iff`: the depth-\(d\) word of \(y\) depends only on
  \(y \bmod 2^d\), and the residue-to-word map is a bijection (mirrors of
  `parityWord_eq_iff` and `image_parityWord`).
- `negT_class_drops`: if the class word has a contracting prefix of length
  \(t\) (\(3^{o_t}<2^t\)), then \(\text{negT}^t(y)<y\) for every \(y\ge1\)
  in the class, with no threshold, because the correction subtracts. This is
  Lemma 5 and the exactness of the residue sieve modulo \(2^{24}\) with
  \(A076227(24)=286581\) classes that the CPU and GPU verifiers use.
- `negT_undecided_card`: the undecided class count modulo \(2^d\) equals
  `neverNegCount d` for \(d=4,\dots,10\) by `decide +kernel`, reproducing
  3, 4, 8, 13, 19, 38, 64.

Buys: the \(2^{51}\) floor's method is kernel-checked; only the machine run
stays computational. Update Paper D Section 8 and
`J-negative-floor-makes-the-mirror-unconditional` to cite it. Size: days.

### 2.4 Four small completions, hours each

- **Exact preimages.** In `Preimages.lean` or an auxiliary file:
  `floorPower n = m` with \(n=m^2\) iff \(m\) even; for odd \(n\),
  `floorPower n = m` with \(n^3=m^2\) iff \(n=s^2\), \(m=s^3\), \(s\) odd.
  Beside it, on the Collatz side: the odd preimage \((2m-1)/3\) exists iff
  \(m\equiv2 \bmod 3\). Records the 3-adic half of
  `J-lemma-eight-is-the-exponent-valuation`; new ledger row.
- **Coefficient identity.** With \(\rho_w=2^{-a}(3/2)^b\) over the rationals,
  \(c_w:=2^{-|w|}/\rho_w=3^{-b}\) (`coefficient_eq_three_pow`), and at every
  finite depth \(\sum_{|w|=d}c_w\rho_w^{\lambda}=\sum_{|w|=d}2^{-d}\rho_w^{\lambda-1}\)
  over the reals with `rpow` (`F_J_eq_F_C_shift`). Moves
  `J-paper-c-ceiling-is-the-collatz-walk-mgf` to Lean.
- **The Collatz exhibit.** A generic `BackwardClosedUnder f A`; the set
  \(\{3\cdot2^k\}\) is backward-closed under `shortcutC` because a multiple of
  three has no odd preimage (\(2\cdot3\cdot2^k-1\equiv2 \bmod 3\)); its
  reciprocal sum is \(2/3\) by the geometric series (`tsum`). Moves
  `J-paper-c-collatz-analogue-is-false-by-exhibit` to Lean and puts the
  Collatz half of the duality beside Paper C's Theorem 1.
- **The mirror identity.** With \(x=\log2/\log3\):
  \(\Lambda_C(L)=L\log2-\lfloor Lx\rfloor\log3=\log3\cdot\{Lx\}\) and
  \(\Lambda_J(L)=\lceil Lx\rceil\log3-L\log2=\log3\cdot(1-\{Lx\})\), hence
  \(\Lambda_J(L)+\Lambda_C(L)=\log3\), using \(Lx\notin\mathbb Z\) from
  \(2^a\ne3^b\). Moves the first half of `J-cycle-gaps-are-mirror-images`
  to Lean.

## 3. Tier 2 — substantive and bounded

- **Catalan for the pair 2 and 3.** \(3^x-2^k=1\) forces
  \((x,k)\in\{(1,1),(2,3)\}\) and \(2^k-3^x=1\) forces
  \((x,k)\in\{(0,1),(1,2)\}\). Elementary: modulo 3 the second forces \(k\)
  even and then \((2^j-1)(2^j+1)=3^x\); modulo 4 the first forces \(x\) even
  for \(k\ge2\) and then \((3^i-1)(3^i+1)=2^k\). Not in Mathlib. A day. Needed
  by Knight's escapes and by the gap-one cases the Lemma 8 row lists.
- **Knight, sign-free** (`J-knight-is-sign-free-and-catalan-bounds-the-escapes`).
  Christoffel words of slope \((k,x)\), the rational cycle value \(f(w)\),
  reversal is a rotation, the identity
  \(3f(v)-f(v^R)+1=2^{k-1}/(2^k-3^x)\), and the gap is odd, so the value is
  not an integer when \(|2^k-3^x|>1\). With the Catalan lemma the expanding
  escapes are \((1,1)\) and \((3,2)\), realized by \(-1\) and \(-5\).
  Result: no aperiodic Christoffel word carries an integer cycle of the
  integer shortcut map beyond \(\{1,2\}\), \(-1\), \(-5\). Since the ceiling
  mechanical word is the cubic-band word a height-bounded Juggler cycle must
  carry, this is the one word-level theorem about the Juggler's own candidate
  word on both signs at once. One to two weeks. It excludes no Juggler cycle;
  say so in the module header.
- **Paper D Lemma 2** in `NegativeMCycles.lean`:
  \(\Lambda=o\log3-K\log2=-\sum\log(1-1/(3y))\) over the odd cycle elements,
  a run from a local minimum contributes less than \(1/(y-1)\), and
  \(\Lambda<\sum_i1/(y_i-1)\le m/(x_{\min}-1)\). The real log and power
  libraries are already imported there. Days to a week. Lemma 6, the valley
  count, afterwards as a finite optimization statement.
- **Convergent alternation.** From `GenContFract.sub_convs_eq` at
  \(v=\log2/\log3\), the convergent denominators fall on alternating sides;
  define the Juggler-side and Collatz-side lengths and prove them disjoint,
  the second half of `J-cycle-gaps-are-mirror-images`. Medium; the API for
  `GenContFract.of` on an irrational real is fiddly.
- **The K-L transposition** (`J-kl-preimage-density-transposes-to-3n-1`): the
  map \(m\mapsto-m\) on `ZMod (3^k)` carries one production system onto the
  other, by `decide` for \(k\le6\) and as a residue theorem in general. Low
  priority: it checks a formal residue transposition, not the
  Krasikov–Lagarias theorem. **Correction of 22 September:** the density
  row was returned to `CONJECTURE`. `Problems/Collatz/PreimageScale.lean` proves
  that the actual minus odd predecessor reverses the height comparison,
  with correction factor 1+1/(2a). Its `finite_expanding_shift` now
  absorbs offsets uniformly through a finite family of expanding inverse
  blocks; `internal_prefix_height` also controls the whole path. The
  strict-grid follow-up `PreimageGrid.lean` proves actual pointwise count
  inequalities and a decreasing induction measure above root 4096,
  avoiding the minimum/deletion operations. `PreimageDomain.lean` now
  closes the domain for every positive target prime to 3, including cycle
  targets, using a finite orbit barrier and a nonperiodic large ancestor.
  A fixed connecting path transfers counts after a fixed cutoff. The
  completed `PreimageCertificate12.ancestor_density_21_25` now proves
  X^21<=ancestorCount(a,X)^25 eventually for every positive unit target.
  Its root induction, all 177147 integer certificate rows, and cutoff
  interpolation are kernel-checked. The row is now `EXACT — HUMAN PROOF`
  pending advisory coverage; the local formal proof is complete. No
  Juggler pressure estimate or termination transfer follows.

## 4. Not in Lean, by decision

- **No realization transport.** Every negative-side statement is about
  `negT` or the integer shortcut map; every Juggler statement is about
  `floorPower`; the only shared hypothesis is a word. A Lean statement that
  pretended otherwise would be false, not merely unproved
  (`J-the-missing-juggler-floor-is-worth-a-quarter-at-length-22`).
- **Rhin's measure stays a hypothesis.** Any Lean statement of Paper D's
  theorem takes the measure as a named proposition. The \(m\le61\)
  enumeration runs over lengths near \(10^{13}\) and is not kernel-feasible;
  the \(2^{51}\) floor stays a certificate.
- **No second copy of `negT`.** Do not restate it inside `Problems.Juggler`
  to satisfy the barrel rule; import `NegativeMCycles` from an auxiliary
  module. The local `shortcutC` copy in `CollatzBridge` was forced by
  compiler-trusted proofs in `Problems.Collatz.Shortcut`, and nothing forces
  one here. A duplicate gives one fact two names.
- **No `native_decide`** anywhere in the Juggler layer.

## 5. Order of work and gates

Order: 2.1, then 2.3, then 2.2, then 2.4; the items are independent except
that the window (2.1, step 3) needs the conjugacy (2.1, steps 1 and 2).

Before each edit: `python tools/formalpedia.py impact <module>` and
`search` for both the object and the result. `CollatzBridge` reaches
`Problems.JugglerPaper`, so its statements are load-bearing for Paper A: add
lemmas, do not restate.

After each edit: `lake env lean <file>`, then `lake build Problems.Juggler`
for an auxiliary module or `lake build Problems.Collatz.NegativeSieve` for the
Collatz-side file; `pytest tests/research/juggler_sequence/test_layer_architecture.py -q`;
`python tools/render_theorem_ledger.py --check` after any ledger row;
`python -m research.juggler_sequence.branch_index --check` if a row's `tests`
list changes; rebuild `attacks/juggler/index.json` for a new Juggler module;
rebuild the formalpedia index only when `git status --porcelain formal/`
shows your own files alone. Stage explicit paths, never `git add -A`.

Ledger: new rows for the window, the sieve and the exact preimages. Retag
`J-cycle-gaps-are-mirror-images`, `J-paper-c-collatz-analogue-is-false-by-exhibit`,
`J-paper-c-ceiling-is-the-collatz-walk-mgf` and
`J-lemma-eight-floor-is-tight-at-every-known-cycle` only after
`python tools/formalpedia.py jev-coverage --rows <id>` on each row alone. For
`J-negative-m-cycle-lemmas`, add the Lean file name now, since
`NegativeMCycles` proves Lemmas 1 and 3, without a retag: the row also states
Lemma 2 and Lemma 6, which are not in Lean.

## 6. What this plan does not claim

No Juggler cycle is excluded, no floor is raised, \(N_0\) is untouched,
Paper A is unchanged, and neither map is claimed to halt. The plan makes the
bridge one machine-checked object and raises the trust level of Paper D's
sieve; it moves no bound in any of the three problems.

## Appendix: two checks of 21 September 2026, not in the repository

Both from scratch scripts, neither run through a probe, neither in the
ledger.

- Exact backward steps of the Juggler below 3000: the even preimage \(m^2\)
  exists iff \(m\) is even, brute force below 60 agrees; the odd preimage
  \(s^2\) exists iff \(m=s^3\) with \(s\) odd, 7 targets below 3000.
- The ceiling Juggler, \(\lceil n^{3/2}\rceil\) on odd \(n\) and
  \(\lceil\sqrt n\rceil\) on even \(n\), reaches only the cycles \(\{1\}\),
  \(\{2\}\) and \(\{3,6\}\) from starts below 3000 under a 400-step cap, and
  \(\{3,6\}\) carries the contracting word `OE` of the Collatz trivial cycle.
  Together with \(-17\) these are the known-bad inputs for any Juggler
  no-cycle argument that does not use the direction of rounding, and they are
  what the `cycle_of_upward` instance of 2.2 would formalize.

The finite-grid mean audit is now compiled in `Problems/Collatz/PreimageBalance.lean`.
Both signs share the all-level necessary inequality
1<=mu^(-100)+(mu^29+mu^(-21))/3. In the at-most-linear rate range,
mu^5000<2^99; the harmonic rate contradicts 2^79<3^50.
This closes table-size growth alone in the current fixed grid, while
actual fate-specific harmonic growth and Juggler pressure remain open.

The arithmetic continuation on the Juggler side is now recorded in
[odd-image discrepancy](../problems/juggler_odd_image_discrepancy.md): a
written square-root-plus-epsilon one-step bound using the rational cubic
dual phase. `Problems/Juggler/OddCubicPhase.lean` verifies the exact
stationary-point algebra and zero complete mean for odd harmonics.
The analytic bound awaits independent review and is not a Lean theorem;
there is no transfer to the growing-depth pressure from this estimate.

`Problems/Juggler/PolynomialDual.lean` identifies the smooth stationary
dual degree denominator with the signed Collatz cycle gap. An elementary
kernel proof classifies integral degrees as 3 and 9, occurring only at
(o,L)=(1,1),(2,3); ninth-degree odd harmonics have zero complete mean.
This closes direct extension of polynomial periodicity to longer smooth
word phases, without ruling out perturbative methods or proving an
actual selected-sum estimate. See
[the bounded decision](../problems/juggler_polynomial_dual.md).

`Problems/Juggler/CubicInverseCell.lean` now checks the exact perturbed
phase, derivative quotients and sign factors, and rational exponent
budget for a first inverse-cell estimate. The mixed-frequency and
weighted bounds are written analytic proofs, not Lean theorems. This
is one quantitative weighted level; further itinerary restrictions
and the growing-depth pressure remain open.
