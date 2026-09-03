# Juggler finite-dynamics formalization map

This page is the Lean companion to the two manuscripts: **Paper A**,
[juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md)
(cycle-length lower bounds; core lemmas Lean-backed, while the
descent floors, Theorems 4.6, 4.8, 5.2, 5.9, and Corollaries 5.10--5.11
are independently certified computations, and Denjoy--Koksma and
the ergodic identification of \(C_*\) are classical prose), and **Paper B**,
[juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md)
(parity discrepancy; human proofs over Lean-verified floor
identities). Both are written to be readable without this page.
Unqualified references to "the note" below mean Paper A. The
development is in `formal/Problems/Juggler/`; it contains no `sorry`
or `admit`. The review object for **Paper A** is the paper barrel
`formal/Problems/JugglerPaper.lean` (`lake build Problems.JugglerPaper`).
That file imports only the modules named by Paper A (Appendix A of
the note), including `CycleFinance.lean` for Theorem 4.4 (the
census and length-exclusion companions live in
`CycleFinanceLeftovers.lean`) and
`RunSurvivorLattice.lean` for Proposition 4.9. It does
not import `GapCells.lean` or `CycleHeightFinance.lean`. Laboratory
satellites remain in `formal/Problems/Juggler.lean` and are not the
review object.

The package formalizes finite trajectories and conditional cycle structure.
It does not prove that every positive integer reaches \(1\), that every trajectory
has a contracting prefix, or that nontrivial cycles are impossible.

The paper-central one-way import graph is drawn in
[figures/juggler_lean_layers.png](figures/juggler_lean_layers.png)
from source [figures/juggler_lean_layers.mmd](figures/juggler_lean_layers.mmd).
Satellite modules omitted from that figure remain in
`formal/Problems/Juggler.lean`.

## 1. Map and iteration

Source: `formal/Problems/Juggler/Dynamics.lean`.

`floorPower` is the integer map
\[
J(n)=
\begin{cases}
\lfloor\sqrt n\rfloor,&n\equiv0\pmod2,\\
\lfloor n^{3/2}\rfloor=\operatorname{isqrt}(n^3),&n\equiv1\pmod2.
\end{cases}
\]

The even and odd branches are implemented by exact natural-number square-root
operations. Positivity, parity-specific bounds, and monotonicity are proved
without floating-point arithmetic.

Iteration and the reachability predicate `ReachesOne` are developed in
`Iteration.lean` and `Termination.lean`. The finite lemmas there are not a
universal termination theorem.

## 2. Itineraries

Source: `formal/Problems/Juggler/Itinerary.lean`.

```text
inductive Branch where | even | odd
bit     : Nat -> Branch
word    : Nat -> Nat -> List Branch
follows : Nat -> List Branch -> Prop
image   : Nat -> List Branch -> Nat
```

The central semantic bridge is

```text
follows_iff_itinerary (n) :
  follows n w ↔ itinerary n w.length = w
```

The endpoint has the intended iterative semantics:

```text
image_eq_iterate (n) :
  image n w = floorPower^[w.length] n
```

Concatenation is exact:

```text
image_append
follows_append
follows_of_append_left
follows_of_append_right
```

In particular, a realized itinerary decomposes into a realized prefix and a
realized suffix from the prefix endpoint.

The fixed-itinerary image is monotone on its realizing set:

```text
image_monotone_of_follows :
  follows n w -> follows m w -> n <= m -> image n w <= image m w
```

This theorem does not say that two different words share a common monotone
extension or that a realizing set is an interval.

## 3. Word statistics and languages

Sources:

- `formal/Problems/Juggler/ItineraryStats.lean`;
- `formal/Problems/Juggler/ItineraryLanguage.lean`;
- `formal/Problems/Juggler/ExpandingGrammar.lean`.

`oddCount w` counts odd letters. The exponent comparison is represented by
\[
3^{\#O(w)}\quad\hbox{versus}\quad2^{|w|}.
\]

The formal languages are existential:

```text
jugglerLanguage w             := ∃ n, follows n w
expandingLanguage w           := ∃ n, follows n w ∧ n < image n w
persistentExpandingLanguage w := ∃ n, follows n w ∧
  PersistentExpandingResidual n (image n w)
```

The realizable language is factor-closed (`jugglerLanguage_factor`), while the
existential expanding language is not
(`expandingLanguage_not_factor_closed`). These predicates must not be replaced
by the syntactic exponent comparison.

## 4. Power envelope and contraction

Source: `formal/Problems/Juggler/Envelope.lean`.

For every realized finite itinerary,
\[
J^{|w|}(n)^{2^{|w|}}\le n^{3^{\#O(w)}}.
\]

Lean:

```text
power_bound_word (hw : follows n w) :
  (floorPower^[w.length] n) ^ (2 ^ w.length) <=
    n ^ (3 ^ oddCount w)
```

The strict contraction corollary is:

```text
power_bound_contracts
  (hn : 2 <= n)
  (hw : follows n w)
  (hgap : 3 ^ oddCount w < 2 ^ w.length) :
  floorPower^[w.length] n < n
```

Thus the exponent gap is sufficient for contraction along a realized itinerary.
No theorem states that every trajectory realizes such an itinerary.

## 5. Exact defects

Sources:

- `formal/Problems/Juggler/Defect.lean`;
- `formal/Problems/Juggler/GlobalDefect.lean`;
- `formal/Problems/Juggler/DefectLowerBound.lean`;
- `formal/Problems/Juggler/NormalizedDefect.lean`.

Local floor loss is represented by branch defects. The branch identity is
the exact equality
\[
x^e=J(x)^2+\rho,
\]
where \(e=1\) on an even step and \(e=3\) on an odd step.

The recursively lifted global defect satisfies:

```text
global_defect_identity (hw : follows n w) :
  n ^ (3 ^ oddCount w) =
    image n w ^ (2 ^ w.length) + globalDefect n w

global_defect_eq_zero_iff_localsTight (hw : follows n w) :
  globalDefect n w = 0 ↔ localsTight n w

global_defect_append (hu : follows n u) (hv : follows (image n u) v) :
  globalDefect n (u ++ v) =
    powGap (image n u ^ (2 ^ u.length)) (globalDefect n u)
      (3 ^ oddCount v) +
    powGap (image (image n u) v ^ (2 ^ v.length))
      (globalDefect (image n u) v) (2 ^ u.length)
```

This is the weighted lift of local remainders, not an additive path sum.
Zero defect recovers local tightness and the rigid monochrome towers. The
normalized-defect and lower-bound modules provide exact consequences of this
identity. They do not turn the defect into a state-independent contraction
budget. The math note now states the identity, vanishing, and composition
as Theorems 2.4--2.6.

## 6. Residual steps and finite progress

Sources:

- `formal/Problems/Juggler/Residuals.lean`;
- `formal/Problems/Juggler/Progress.lean`;
- `formal/Problems/Juggler/Minimal.lean`;
- `formal/Problems/Juggler/FirstPassage.lean`.

`ResidualStep x y` records a realized block \(O^aE^b\), with \(b\ge1\),
whose endpoint is \(y\). `ResidualChain`, `ReturnBelow`,
`PersistentOddResidual`, and `PersistentExpandingResidual` package finite
first-return structure.

Representative exact results include:

```text
odd_even_residual_trichotomy
minimal_first_even_dichotomy
residualStep_global_defect
two_block_ooe_365
```

The last theorem certifies the persistent expanding chain
\[
365\xrightarrow{OOE}763\xrightarrow{OOE}1749.
\]

`FiniteProgress` is an abbreviation of `DescentCertificate`. The four
constructors are proof forms of the English descent certificate (image
strictly below the start, or image `1`), not four different claims.
`MinimalNonTerm` and the coefficient-stop statements separate a sufficient
finite descent certificate from the unproved universal claim. In particular,
`MinimalImpliesCoeffStop` is a proposition, not a proved theorem.

The exact induction boundary is:

```text
reachesOne_of_all_finiteProgress :
  (∀ n, 1 < n -> FiniteProgress n) ->
  ∀ n, 1 <= n -> ReachesOne n

even_finiteProgress :
  2 <= n -> n % 2 = 0 -> FiniteProgress n

odd_even_finiteProgress :
  2 <= n -> n % 2 = 1 -> floorPower n % 2 = 0 ->
  FiniteProgress n

no_finiteProgress_implies_odd_odd :
  2 <= n -> ¬FiniteProgress n ->
  n % 2 = 1 ∧ floorPower n % 2 = 1
```

Thus even and odd-to-even starts have automatic finite progress. The
density corollaries of the companion discrepancy paper (\(3/4\) at two
steps, \(13/16\) at four, \(7/8\) at five, \(57/64\) at seven,
\(29/32\) at eight) count uniform certificate classes. They
are not Lean cardinality theorems, not densities of all
`FiniteProgress`, and not `ReachesOne` densities. Odd-to-odd starts
may still descend after a longer word. The Terras analogue remains
open; Paper B's Proposition 7.1 reduces it to all-depth parity
equidistribution, which is now proved at every depth \(\le4\)
(including the \(OOO*\) split via the kernel theorem, Paper B's
Theorems 5.3 and 6.1); the first open case is the \(OOOO*\) split
(Paper B's Conjecture 7.3).

## 7. Exact one-step preimages

Sources:

- `formal/Problems/Juggler/Preimages.lean`;
- `formal/Problems/Juggler/PreimageCylinders.lean`.

The one-step fibers are:
\[
J(n)=q\iff q^2\le n<(q+1)^2
\quad(n\ {\rm even}),
\]
and
\[
J(n)=m\iff m^2\le n^3<(m+1)^2
\quad(n\ {\rm odd}).
\]

Lean names:

```text
even_preimage_iff
odd_preimage_iff
odd_preimage_unique
```

`odd_preimage_unique` proves that an odd one-step preimage contains at most one integer.
Even one-step preimages can contain many even predecessors. This is the exact one-step-preimage
asymmetry used in the paper.

`squareCylinder` and `wordCylinder` iterate the one-step-preimage semantics. The theorem

```text
ooe_cylinder_both_next_parities
```

certifies two `OOE` cylinders, at starts \(3461\) and \(3803\), whose next
landings have opposite parity. It is a counterexample to treating the tested
cylinder data as a complete next-parity state.

## 8. Cycles

Sources:

- `formal/Problems/Juggler/Residuals.lean`;
- `formal/Problems/Juggler/Cycles.lean`;
- `formal/Problems/Juggler/LeftoverEval.lean`;
- `formal/Problems/Juggler/LeftoverCycles.lean`;
- `formal/Problems/Juggler/LeftoverTwoEven.lean`;
- `formal/Problems/Juggler/FirstETransport.lean`;
- `formal/Problems/Juggler/BunchedEEE.lean`;
- `formal/Problems/Juggler/BunchedEOEE.lean`;
- `formal/Problems/Juggler/BunchedEOOEE.lean`;
- `formal/Problems/Juggler/BunchedEEOE.lean`;
- `formal/Problems/Juggler/BunchedEOEOE.lean`;
- `formal/Problems/Juggler/BunchedEOOOEE.lean`;
- `formal/Problems/Juggler/BunchedEOOEOE.lean`;
- `formal/Problems/Juggler/SmallCycleCensus.lean`.

```text
CycleItinerary n w :=
  follows n w ∧ image n w = n ∧ 1 <= w.length
```

Every nontrivial cycle itinerary based at \(n\ge2\) is formally expanding:

```text
cycle_itinerary_formally_expanding :
  2 ^ w.length < 3 ^ oddCount w
```

A realized path from \(n\ge 2\) to a state at least \(n^2\) is
superquadratic, and the path from a cycle minimum to any later even
state is superquadratic:

```text
square_scale_superquadratic :
  2 ^ (w.length + 1) ≤ 3 ^ oddCount w
cycleMin_to_even_superquadratic
```

The formal cycle stack also includes:

```text
cycle_pow_le_lowerDenom
cycleMin_start_odd
cycleMax_start_even
cycle_peak_descent
cycle_remainder_balance
cycle_distinguished_order
```

`cycle_distinguished_order` packages the nested order and one-step-preimage relations among
the cycle minimum, maximum, peak predecessor, and return landing.

Two recent boundary lemmas are:

```text
cycleMin_not_end_odd
cycleMin_prefix_ooo_even_sqrt_ne
```

They constrain a minimum-based orientation. The note's Section 3
motivation cites the threshold eliminations of the other expanding
even-terminating length-six candidates:

```text
no_cycleMin_oeoooe
no_cycleMin_ooeooe
no_cycle_odd_run_append_even
```

The two surviving orientations are then excluded separately:

```text
no_cycle_itinerary_oooeoe
no_cycle_itinerary_ooooee
```

The finite range \(n<256\) is evaluated in `LeftoverEval.lean`.
`native_decide` checks both `Fin 256` itinerary-and-return tables and the
finite numerical inequality \(257^{64}<2\cdot256^{64}\). The tail
\(n\ge256\) uses the last-even one-step preimage against the coarse lower envelope
`LowerPowerBound`, via \(n^{81}>2^{130}(n+1)^{64}\).

`SmallCycleCensus.lean` assembles these exclusions into the census of
the note's Theorem 3.6:

```text
no_cycle_itinerary_length_le_six :
  2 <= n -> w.length <= 6 -> ¬CycleItinerary n w
```

Its components are:

```text
replicate_odd_image_gt
no_cycle_itinerary_replicate_odd
rotateItinerary_eq_drop_append_take
exists_even_getElem_of_oddCount_lt
cycleItinerary_exists_even_terminating
no_cycle_itinerary_len_six_ends_even
```

together with the existing `cycleItinerary_rotateItinerary`,
`no_cycle_itinerary_ooe`, `no_cycle_itinerary_length_four_ends_even`,
`no_cycle_itinerary_length_five_ends_even`, `no_cycle_odd_run_append_even`,
`no_cycle_itinerary_ooeooe`, `no_cycle_itinerary_oooeoe`, and
`no_cycle_itinerary_ooooee`.

The same file then strengthens the census to the note's Theorem 3.8:

```text
no_cycle_itinerary_length_le_seven :
  2 <= n -> w.length <= 7 -> ¬CycleItinerary n w
```

The length-seven leftovers are evaluated in `LeftoverEval.lean`
(`Fin 14` tables and `2^422 * 15^128 < 14^243`) and excluded in
`LeftoverCycles.lean`:

```text
no_cycle_itinerary_oooooee
no_cycle_itinerary_ooooeoe
```

The internal-E bootstrap pair is excluded in `Cycles.lean`:

```text
no_cycle_itinerary_ooeoooe
no_cycle_itinerary_oooeooe
```

The itinerary census of Theorems 3.6 and 3.8 is the elementary layer
through length seven. Theorems 3.12--3.21 assemble as Paper A
Theorem 3.22: no cycle itinerary has even-count at most three, so a
nontrivial cycle has period at least eleven. Section 4 excludes
later periods by financing. It is not an exclusion of all leftover
lengths and not a halt theorem.

The note's family theorems after the census are:

```text
cycle_trailing_evens_lt          (Lemma 3.9)
lowerDenom_replicate_odd
odd_run_lower_growth             (Lemma 3.10)
no_follows_seven_odds_of_lt256   (Lemma 3.11)
no_cycle_itinerary_two_even_ee
no_cycle_itinerary_two_even_eoe       (Theorem 3.12)
no_cycleMin_gapped_three_even_ee
no_cycleMin_gapped_three_even_eoe (Theorem 3.13; CycleMin only)
no_cycle_itinerary_three_even_eee     (Theorem 3.14)
no_cycle_itinerary_three_even_eoee    (Theorem 3.15)
no_cycle_itinerary_three_even_eooee   (Theorem 3.16)
no_cycle_itinerary_three_even_eoooee  (Theorem 3.17)
no_cycle_itinerary_three_even_eeoe    (Theorem 3.18)
no_cycle_itinerary_three_even_eoeoe   (Theorem 3.19)
no_cycle_itinerary_three_even_eooeoe  (Theorem 3.20)
no_cycle_itinerary_gapped_three_even_ee
no_cycle_itinerary_gapped_three_even_eoe (Theorem 3.21)
no_cycle_itinerary_even_count_le_three (Theorem 3.22)
cycle_itinerary_length_ge_eleven      (Corollary 3.23)
```

Theorem 3.13 is a minimum-based exclusion. It is not a `CycleItinerary`
theorem at a non-minimum start. Theorem 3.21 upgrades those same
words to `CycleItinerary`s by rotation. Theorem 3.22 assembles
Theorems 3.12--3.21 as an even-count exclusion. It is not a
length-9 or length-10 itinerary census.

The cycle-surplus identity of the note's Corollary 2.7 and the
per-step scale bound are:

```text
image_eq_start_defectRatio :
  follows n w -> image n w = n ->
  globalDefect n w = formalSurplus n w
    (NormalizedDefect.lean)

one_plus_eta_lt_succ_sq :
  follows x [b] -> x ^ branchExp b < (floorPower x + 1) ^ 2
    (NearTightScale.lean)
```

The certified four-block expanding chain named in Paper A's Section 5
is `four_block_pe_1999` in `ExpansionSlack.lean`.

The financing inequality of Paper A's Theorem 4.4 is a cycle leaf
under this barrel:

```text
cycleMin_finance :
  CycleMin n w ->
  n * log n * (3^oddCount w - 2^w.length) ≤ w.length * 3^oddCount w
    (CycleFinance.lean; Paper A Theorem 4.4; constant 1)

cycleMin_finance_inv_sum :
  CycleMin n w ->
  (3^oddCount w - 2^w.length) * log n ≤
    3^oddCount w * ∑ 1 / floorPower^[i+1] n
    (CycleFinance.lean; Paper A Corollary 4.4c)
```

The run-type packing (Paper A Theorem 4.7) and the \(99\)-length
table (Theorem 4.8) are not Lean. The lattice arithmetic of
Proposition 4.9 is a cycle leaf under this barrel:

```text
run_survivor_unimodular :
  Lstar * Ostep - Lstep * Ostar = 1
run_survivor_seed_F2 :
  latticePoint 2 (-1) = (50508, 31867)
run_survivor_seed_F3 :
  latticePoint 3 (-1) = (76289, 48133)
three_pow_step_gt_two_pow_step :
  3 ^ 665 > 2 ^ 1054
runSurvivors_length :
  runSurvivors.length = 99
    (RunSurvivorLattice.lean)
```

Those identities organise \(\mathcal E_{\mathrm{run}}\). They do
not constrain an actual cycle. The identification of the \(99\)
lattice points with the run-type table is Theorem 4.8, not Lean.

The floor-free gap transfer (Theorem 4.10) is a second cycle leaf
under this barrel:

```text
cycleMin_gap_transfer (hn : 2 ≤ n) (h : CycleMin n w) :
  n * log n * min (oddCount w * log 3 - w.length * log 2) 1
    ≤ 2 * w.length
cycleMin_length_of_gap (hn : 2 ≤ n) (h : CycleMin n w)
    (hε : ε ≤ 1)
    (hgap : ε ≤ oddCount w * log 3 - w.length * log 2) :
  n * log n * ε ≤ 2 * w.length
    (GapTransfer.lean)
```

Corollary 4.11 instantiates `cycleMin_length_of_gap` with Rhin's
effective measure \(\varepsilon=e^{-6.1256}L^{-13.3}\); that
transcendence input is classical and is a hypothesis, not a Lean
theorem. The corollary is a reduction (short cycles
\(L^{14.3}\le n\log n/915\) are excluded for all \(n\ge 2\)), not a
period bound at any floor.

Companion names leftover \(84\), residual floor \(261\), and the
census through length \(19\) are listed in Appendix A of the note
and live in `CycleFinanceLeftovers.lean` (table-driven length
exclusions over `financeRows53` / `financeRows257` /
`financeRows261`). They are not paper theorems.
`CycleHeightFinance.lean` is not imported.

## 8.5 Excursion necklace

Paper A Section 4 now opens with the excursion necklace of a
minimum-based cycle itinerary. That subsection is organizing prose:
it names the circular itinerary already implied by Theorem 3.2,
Lemma 3.4, Lemma 3.21b, and the last-even one-step preimage. It introduces
no new theorem and no new Lean object. The table below records
how each stage is represented. Names marked *satellite* are
not imported by `Problems.JugglerPaper` and are not in
Appendix A of the note.

The itinerary is
\[
n
\;\xrightarrow{\;OO\;}
\text{first high region}
\;\xrightarrow{\;E\;}
v_1
\;\xrightarrow{\;O^{a_2}E\;}
\cdots
\;\xrightarrow{\;O^{a_e}E\;}
n,
\]
with valleys \(v_i\), peaks \(p_i=J^{a_{i+1}}(v_i)\), and
\(v_{i+1}=\lfloor\sqrt{p_i}\rfloor\).

| Stage | Lean (barrel unless marked) | Code | Status |
|---|---|---|---|
| Cycle minimum \(n=\min C\) | `CycleMin`, `cycleMin_start_odd`, `cycleMin_ge`, `aboveAnchor_of_cycleMin`, `exists_cycleMin` (`CycleCore.lean`) | `cycle_extrema.stay_above_min_excursion`; finance tables at a CycleMin start | **EXACT — LEAN VERIFIED** (Theorem 3.2(ii)) |
| Forced prefix `OO`; no `OE` start | `cycleMin_not_odd_even`; `cycleMin_oddEvenBlock_starts_two_odds` (`EvenCountThree.lean`) | leftover scanners rotate to a start-`OO` orientation | **EXACT — LEAN VERIFIED** |
| First lift; \(J^2(n)\ge(n+1)^2\) | `oo_suffix_threshold`, `ooo_suffix_threshold`, `threshold_inherits_odd_append`; `no_cycle_itinerary_ooe` | `power_itineraries.floor_power` | **EXACT — LEAN VERIFIED** (Lemma 3.4) |
| First peak overshoots the entry one-step preimage | `cycleMin_first_even_overshoots`, `cycleMin_max_ge_succ_sq`, `cycleMin_to_even_superquadratic` | — | **EXACT — LEAN VERIFIED**. Opposite of the last-peak one-step preimage |
| Block \(O^aE\) | `oddEvenBlock a 1` (`ItineraryStats.lean`); `exponentExpanding_oddEvenBlock`. Satellite: `oe_block_contracts` (`Scale.lean`) | `cycle_ordered_excursion.excursion_map` (the laboratory \(F_a\); not a Lean name) | Block language **EXACT — LEAN VERIFIED**. \(\mu(a)=3^a/2^{a+1}\) is a **REPARAMETERIZATION** of the itinerary envelope |
| `OE` contracts, `OOE` expands | \(\mu(1)=3/4\), \(\mu(2)=9/8\); `no_cycle_odd_run_append_even` forbids \(O^aE\) as a *cycle itinerary* for \(a\ge 3\), not as an internal block | `odd_run_itinerary.block_lambda` | same |
| Square-preimage gap \(243<256\) | Satellite: `follows_ooeooeo_image_lt_sq` (`Escape.lean`) | inherited corridor on `OOEOOEO` | not a CycleMin theorem; not Appendix A |
| Repeated expanding blocks | Satellite: `two_block_ooe_365`, `expanding_type_ooe_self_loop` (`Residuals.lean` / `ExpandingGrammar.lean`); barrel: `four_block_pe_1999` | `odd_run_itinerary.py` controls; Paper A §5 uses \(1999\) | **OBSERVATION** on residuals. \(1517\) is not in Lean |
| Valley skeleton \(\sum a_i=o\), \(e=L-o\) | Lemma 3.21b in prose; `oddEvenBlock` concatenation. Satellite: `dropOddRun`, `cycleCircuitCount` (`CycleHeightFinance.lean`) | `cycle_almost_search.circuits`, `packed_block_word`; `cycle_budget_opt.run_type_counts` | **EXACT — HUMAN PROOF**. No Lean `F_a` or `Valley` |
| Peaks \(p_i\); every even state \(\ge n^2\) | `cycleMin_max_gt_sq`, `cycleMin_to_even_superquadratic` (`CycleExtrema.lean`) | `cycle_peak_descent.py`; evens charged at \(n^2\) in `cycle_budget_opt` | **EXACT — LEAN VERIFIED**. Peak-count theorems stay out of the note |
| Finance on the wave | `cycleMin_finance`, `cycleMin_finance_inv_sum` (`CycleFinance.lean`) | `cycle_finance.py`; `cycle_budget_opt.py` | Theorem 4.4 **EXACT — LEAN VERIFIED**; 4.7 human; 4.6/4.8 computational |
| Last peak / entry one-step preimage | `cycle_last_even_interval`, `cycle_last_even_ne_odd_sq`, `cycle_trailing_evens_lt`, `cycleMin_not_end_odd` | `cycle_entry_excursion.entry_even_preimage` | Cell **EXACT — LEAN VERIFIED**. Enumerated fibres are archived laboratory negative knowledge |
| Circular closure / necklace | `rotateItinerary`, `cycleItinerary_rotateItinerary`, `cycle_iterate_period` | `cycle_cyclic_valley.py` (archived) | rotation **EXACT — LEAN VERIFIED**. No Lean `Necklace` |
| \(L_*=25781\) in Lean | `Lstar`, `Ostar`, `runSurvivors_length` (`RunSurvivorLattice.lean`) | `budget_opt.json` leftover \(99\) | Lattice generator, **not** the period bound. The bound is Theorem 4.6 |
| Later leftover-killers | not in the paper barrel | `cycle_entry_excursion`, `cycle_inverse_width`, `cycle_trajectory_budget`, `cycle_cyclic_valley`, `cycle_realizable_finance`, `cycle_extremizer_discrepancy`, … | all **CLOSE** / **REFUTED**. Recovered Theorem 4.7 or closed. Not paper claims |

The first peak and the last peak are different even states. On a
`CycleMin` the first even residual satisfies \(p_0\ge(n+1)^2\).
The last even residual occupies \(n^2\le p_{e-1}<(n+1)^2\).
Do not write “the CycleMin peak lies in the first square one-step preimage.”

The remaining gap recorded in the note is the missing implication
from the forced lift, the complete necklace, and the entry one-step preimage
to a contradiction on leftover lengths. There is no such Lean
theorem.

## 8.7 Walk-charge words and Ostrowski arithmetic (Paper A Section 5)

Sources: `formal/Problems/Juggler/WalkChargeItineraries.lean`,
`formal/Problems/Juggler/OstrowskiSandwich.lean` (both in the paper
barrel since the 1 September 2026 consolidation).

`WalkChargeItineraries.lean` certifies the discrete side of Paper A
Lemma 5.6 and the combinatorial core of Theorem 5.4. The exact hug
rule (even at position \(k\) with \(a\) odd letters used iff
\(2^{k+1}\le 3^a\)) keeps the odd count in the unit window
\(2^k\le 3^{\mathrm{hugOdds}(k)}<3\cdot 2^k\)
(`hugOdds_pow_ge`, `hugOdds_pow_lt`), is minimal among admissible
budgets (`hugOdds_least`, the integer form of
\(o_{\min}(k)=\lceil k\log 2/\log 3\rceil\)), is prefix-minimal among
admissible exponent walks (`hugOdds_le_of_admissible`), and the
budgeted hug itinerary at \((L,\mathrm{hugOdds}(L))\) equals the exact
rotation prefix (`budgetedWord_eq_hugWord`). Sanity instances
\(\mathrm{hugOdds}(84)=53\), \(\mathrm{hugOdds}(1054)=665\),
\(\mathrm{hugOdds}(50508)=31867\) match the finance table.

Two corollaries are Lean end to end. Cycle-itinerary domination
(`cycleMin_prefix_odds_ge_hug`, `cycleMin_odds_ge_hug`): every
prefix of a minimum-based cycle itinerary carries at least
\(\mathrm{hugOdds}(k)\) odd letters, by composing the cycle prefix
envelope `cycleMin_prefix_pow_le` (CycleCore) with
`hugOdds_least`; the strict window `hugOdds_pow_gt` identifies
\(\mathrm{hugOdds}\) with the strict \(o_{\min}\). Lattice bridge:
the survivor-lattice generators of Proposition 4.9 lie on the hug
diagonal \(o=o_{\min}(L)\) — \((1054,665)\), \((25781,16266)\),
\((50508,31867)\) (`hugOdds_1054`, `hugOdds_lattice_base`,
`hugOdds_seed`, list form `hugOdds_convergent_denoms`). The
Laplace integral (Proposition 5.5) is a human proof.

`WalkTransport.lean` proves the transport inequality of Theorem 5.3
end to end in log form. The walk weight \(w_k=2^{u_k}=3^{a_k}/2^k\)
is rational, so no real exponentiation is needed. The single
transport induction runs on the never-descending hypothesis
`AboveAnchor` (`aboveAnchor_transport`:
\(w_k(\ln n-D)\le\ln x_k\) with
\(D=1.05e/n+0.7o/(n\sqrt n)\) for any descent-free prefix at anchor
\(n\ge 400\)); the paper's `cycleMin_transport` is the closed
instance via `aboveAnchor_of_cycleMin`, since a minimum-based cycle
is a descent-free prefix that returns. Ingredients: per-step floor
losses
\(\ln T(x)\ge\tfrac32\ln x-1.05/(x\sqrt x)\) (odd, \(x\ge 9\)) and
\(\ln T(x)\ge\tfrac12\ln x-1.05/\sqrt x\) (even, \(x\ge 441\))
from the floor one-step preimages and the parameterized majorant
\(-\ln(1-t)\le ct\) on \(t\le 1-1/c\)
(`log_floorPower_odd_ge`, `log_floorPower_even_ge`,
`neg_log_one_sub_le_mul`; instances \(c=1.05\) here and \(c=6/5\)
in DefectFinance); the exact weight recursion
\(w_{k+1}=\tfrac32 w_k\) (odd), \(w_k/2\) (even); odd injections
priced at \(x_j\ge n\) (`aboveAnchor_iterate_ge`) against
\(w_{j+1}\ge\tfrac32\), even injections at \(x_j\ge n^2\)
(`even_ge_sq_of_aboveAnchor`) against \(w_{j+1}\ge 1\)
(`one_le_walkWeight_aboveAnchor`, from `aboveAnchor_prefix_pow_le`,
`CycleCore.lean`). The anchor-free upper side
`follows_log_le_walkWeight` (floors only lose) completes the
fly-height sandwich `aboveAnchor_flight_envelope`.

`WalkChargeMax.lean` closes the chain from transport to the hug
charge (the §5.2 consequence and the analytic half of Theorem 5.4).
The per-state charge is written through the rational weight,
\(\mathrm{stateCharge}\ \nu\ W=1/(e^{W\nu}W\nu)\) — the paper's
\(g(u)=1/(n'^{2^u}2^u\ln n')\) with \(W=2^u\), \(\nu=\ln n'\) —
and is antitone in the weight by elementary \(\exp\) monotonicity
(`stateCharge_antitone`; no charge integral). Composed with
`hugOdds_le_of_admissible`, the exact hug itinerary maximises the total
charge over *all* admissible exponent walks (`hug_charge_maximal`),
a strengthening of the fixed-\((L,o)\) paper statement. Composed
with `cycleMin_transport`: on a CycleMin cycle at \(n\ge 400\) with
positive reduced log-base \(\nu=\ln n-D\), the cyclic defect sum
satisfies \(\sum_k 1/(x_k\ln x_k)\le\sum_k g(w_k)\le\sum_k
g(\mathrm{hugWeight}\ k)\) (`cycleMin_defect_le_charge`,
`cycleMin_defect_le_hug_charge`). What remains human in the §5
chain: the rotation average (Proposition 5.5), Denjoy–Koksma
(Theorem 5.7), the strict within-\((L,o)\) uniqueness of the
maximiser, and the final kill evaluations of Theorems 5.2/5.9
and Corollaries 5.10--5.11 (verified computation).

`DefectFinance.lean` closes the finance side. The certified identity
of Theorem 4.6 — \(1-2^L/3^o\le\tfrac65\sum_k 1/(x_k\log x_k)\) on
any minimum-based cycle at \(n\ge 400\) — is Lean
(`cycleMin_defect_finance`). Ingredients: the per-step floor losses
in image form, \(\varepsilon\le\tfrac65/T(x)\) from
\(\delta\le 2/T(x)\) and \(-\log(1-\delta)\le\tfrac65\delta\) on
\([0,1/6]\) (`log_floorPower_even_ge_sub`,
`log_floorPower_odd_ge_sub`, `neg_log_one_sub_le_sixth`), the
floor-only-loses upper bounds (`log_floorPower_even_le`,
`log_floorPower_odd_le`), and the `WalkTransport` weight induction
run twice: an upper invariant \(\log x_k\le w_k\log n\)
(`cycleMin_log_le_weight`) pricing the amplification and a charged
lower invariant (`cycleMin_charge_prefix`), closed at \(x_L=n\).
Chaining with `cycleMin_defect_le_hug_charge` yields the **kill
criterion** (`cycleMin_hug_kill_criterion`): every minimum-based
cycle at \(n\ge 400\) with positive reduced log-base satisfies
\(1-2^L/3^o\le\tfrac65\sum_k g(\mathrm{hugWeight}\ k)\) at the
reduced base — the full finance-versus-hug-charge implication of
Theorem 5.9 as one Lean theorem. The per-length numeric kill
evaluations and the parity refinement of Corollary 4.5 remain
verified computation.

`OstrowskiSandwich.lean` certifies the quotient arithmetic of
Theorem 5.7: the big-integer sandwich
\(3^{10781274}<2^{17087915}\), \(2^{16785921}<3^{10590737}\)
(`theta_sandwich_upper`, `theta_sandwich_lower`), the real bounds
\(6195184/16785921<\log(3/2)/\log 3<6306641/17087915\)
(`lower_lt_walkTheta`, `walkTheta_lt_upper`), the shared
continued-fraction prefix \([2,1,2,2,3,1,5,2,23,2,2,1]\) of both
rational endpoints (`cf_lower_prefix`, `cf_upper_prefix`,
`cf_lower_continues`, `cf_upper_continues`), and the convergent
denominator list \(1,\ldots,176251\)
(`theta_convergent_denominators`). The digit scan of Theorem 5.8 is
also Lean: for every window length \(50508\le L<301994\) the greedy
Ostrowski digits over the certified denominators reconstruct \(L\)
and sum to at most \(37\) (`window_digit_scan`, pointwise
`window_digit_cap`), attained at \(L=275632\) (`window_digit_max`).
The Denjoy–Koksma hypotheses are certified as well: the matching
numerator list \(0,1,1,3,7,24,31,179,389,9126,18641,46408,65049\)
(`theta_convergent_numerators`, `thetaConvergents_eq_zip`),
unimodularity \(p_{j+1}q_j-p_jq_{j+1}=(-1)^j\)
(`theta_convergents_unimodular`), coprimality
(`theta_convergents_coprime`), the approximation quality
\(|\theta-p/q|<1/q^2\) for all thirteen certified pairs against the
sandwich bounds (`theta_convergent_quality`), and the
block-permutation fact that multiplication by \(p\) permutes
\(\mathbb{Z}/q\) (`residue_mul_bijective`,
`theta_block_permutations`).

`RotationAverage.lean` proves the quantitative half of
Proposition 5.5: for every \(\nu>0\) the rotation average
\(C_*(\nu)=(1/\ln 3)\int_1^3 e^{\nu(1-t)}t^{-2}\,dt\) satisfies
\(C_*(\nu)<1/(\ln 3\,\nu)\) and the sharper Laplace bound
\(C_*(\nu)\le(1-2/\nu+6/\nu^2)/(\ln 3\,\nu)\), with the gap form
\((2/\nu-6/\nu^2)/(\ln 3\,\nu)\le 1/(\ln 3\,\nu)-C_*(\nu)\)
consumed by Theorem 5.8 (`rotation_average_lt`,
`rotation_average_le`, `rotationAverage_lt`, `rotationAverage_le`,
`rotationAverage_gap`). There is no quadrature: the quadratic
majorant \(t^{-2}\le 1-2(t-1)+3(t-1)^2\) on \([1,3]\)
(`inv_sq_le_quad`; the product with \(t^2\) is
\(1+4(t-1)^3+3(t-1)^4\ge 1\)) reduces the bound to an exact
fundamental-theorem-of-calculus evaluation with explicit
antiderivative (`quadPrim`, `hasDerivAt_quadPrim`), whose boundary
term \(-e^{-2\nu}(9/\nu+10/\nu^2+6/\nu^3)\) drops with the right
sign. The ergodic identification of \(C_*\) as the infinite-hug-itinerary
average (unique ergodicity of the rotation) stays prose (KNOWN).

`OstrowskiNumeration.lean` proves the digit-cap step of Theorem 5.8
in general form: for any denominator sequence \(q\) with \(q_0>0\),
\(q\) monotone, and the convergent recurrence bound
\(q_{j+1}\le a_{j+1}q_j+q_{j-1}\), greedy digits from any
\(L<q_{n+1}\) obey the remainder invariant (`ostroRem_lt`), the
structural cap \(b_j\le a_{j+1}\) (`ostroDigit_le`), exact
reconstruction \(L=\sum_j b_jq_j\) when \(q_0=1\) (`ostro_sum_eq`),
and the digit-sum cap (`ostro_digitSum_le`). The \(\theta\) instance
closes the window at \(q_{13}=301994\) and gives \(s(L)\le 47\) for
*every* \(L<301994\), structurally (`theta_digitSum_le`,
`theta_sum_eq`); a `native_decide` bridge identifies the function
form with the fold form `greedyDigitSum` below the window endpoint
(`greedy_eq_ostro_below_window`, corollary `greedyDigitSum_le`).
Denjoy–Koksma's variation-versus-integral inequality and the
cylinder-interval bridge from the endpoints
to \(\theta\) itself are classical and stay prose; the
Denjoy–Koksma comparison and the kill tables (Theorem 5.9,
Corollaries 5.10--5.11) are human proof plus certified computation, not
Lean (the kill *template* is: `cycleMin_hug_kill_criterion`).

## 9. Exact floor reductions for the discrepancy paper

Source: `formal/Problems/Juggler/GapCells.lean`.

Every analytic estimate of Paper B is a human proof. The
exact floor reductions beneath them are Lean-verified over the reals:

```text
floor_odd_iff_half_le_fract_half :
  ⌊x⌋ % 2 = 1 ↔ 1 / 2 ≤ Int.fract (x / 2)

floor_add_eq_add_carry :
  ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ +
    if 1 ≤ Int.fract x + Int.fract y then 1 else 0

floor_gap_eq_carry :
  ⌊x + δ⌋ - ⌊x⌋ = ⌊δ⌋ +
    if 1 - Int.fract δ ≤ Int.fract x then 1 else 0

seq_floor_gap : (the same identity along any sequence Y : ℕ → ℝ)

seq_floor_gap_second : (the double-gap identity: the second
  difference of the level-2 gap is the floor of the double increment
  plus a 0/1 carry plus the difference of two Lemma-N carries; two
  composed instances of seq_floor_gap)
```

The first is the parity bridge that converts parity sums into interval
discrepancies (Paper B's fractional-part form, Lemma 3.2). The gap
identities are the cell structure of Paper B's Lemma 4.3(ii) and
Lemma 5.1(ii) and of the working document's Lemmas B, N, and R2: the
increment of a floored smooth sequence is the floor of the smooth
increment plus a 0/1 sawtooth carry, and the second difference
composes two such identities (used by the kernel theorem, Paper B's
Theorem 5.3). No Vaaler, van der Corput, or Erdős–Turán content is
formalized.

## 10. Evidence boundary

Lean certifies the definitions and theorem statements above. It does not
certify:

- finite first-return counts used in the laboratory (exact Python
  integers; not a claim of Paper A);
- the analytic discrepancy estimates of Paper B (Theorems 4.1, 4.4,
  4.7, 4.8, Proposition 4.5, Corollary 4.9; the level-2 wave
  Lemma 5.2 and the kernel Theorem 5.3 with Corollary 5.4; the depth-4
  completion Theorem 6.1 and the contracting splits Theorems 6.2–6.4
  with Corollary 6.5 — ledger rows `J-kernel-cancellation`,
  `J-depth4-complete`, `J-five-step-descent-density`,
  `J-depth7-engine-contracting`, `J-depth8-engine-quartet`,
  `J-eight-step-descent-density`; Proposition 7.1; and the
  shift-average Theorem 7.4, ledger row
  `J-shift-average-square-root` — all human proofs resting on the
  Lean floor reductions above);
- the scaled-integer validators for the exact-linearization lemmas
  and the kernel, shift-average, and pure-model probes
  (those are pytest-pinned computations, not proofs);
- statistical drift estimates;
- universal Juggler termination.

Those claims have separate evidence labels and reproducibility records in the
paper and its [reviewer packet](juggler_finite_dynamics_reviewer_packet.md).
