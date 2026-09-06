# Declaration review queue

Rows where one candidate leads its file clearly.  Each entry is the ledger row's own
statement beside the candidate's docstring; the question is only whether they say the
same thing.  The scorer was measured at 96% precision on rows with a known answer, so
roughly one in twenty-five of these is wrong -- reading is the point, not rubber-stamping.

40 rows below, of 156 unresolved.

A second failure mode is not scored at all: some rows are composite, and their top
candidate is only the headline theorem.  `BTC-select3` below reads "select3 represents
every Trit->Z map; abs/min/max" -- four theorems, of which `select3_represents` is one.
Accepting it would record a part as the whole.  If the row says "and", ";" or lists
several claims, it belongs in neither column yet.

Answer by adding `decl` and `lean_trust` to the row in `docs/theory/theorem_ledger.json`.

## 1. `BTC-select3`

**Row.** select3 represents every Trit→ℤ map; abs/min/max

**Candidate.** `select3_represents` &mdash; kernel-checked, `BTCalculus/Select.lean:33`

> Every function ``Trit → ℤ`` is ``select3`` of its three values.

*Runners-up: `select3_minus` (0.182), `select3_zero` (0.182)*

*If this row describes a definition rather than a theorem: `select3`, `absZ`*

## 2. `BTA-x3-newton`

**Row.** Newton coordinates of a cubic and of the residual family of x^3

**Candidate.** `newton_cubicResid` &mdash; kernel-checked, `BTCalculus/CubicResidual.lean:269`

> Newton coordinates of the residual family, written in terms of `m` and `p`.

*Runners-up: `eval_cubicResid_iter` (0.3), `residualAlong_cubic_family` (0.25)*

*If this row describes a definition rather than a theorem: `cubicResid`, `newtonCoords`*

## 3. `BTA-x3-n2`

**Row.** same-depth N2 is 3^{k-m-1}|(p-q); injective on P_m if 2m+1<=k

**Candidate.** `sameDepth_n2_injective` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:101`

No docstring; the statement itself:

```lean
theorem sameDepth_n2_injective {k m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (hmk : 2 * m + 1 ≤ k)
    (hN2 : (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q) :
    p = q
```

*Runners-up: `sameDepth_n2` (0.5), `sameDepth_n2_of_le` (0.5)*

*If this row describes a definition rather than a theorem: `balWidth`, `n2Resid`*

## 4. `BTA-x3-sign`

**Row.** odd pair: N2 iff N1; N0 iff 3^k divides D^m(p^3)

**Candidate.** `n3_dvd_iff` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:128`

No docstring; the statement itself:

```lean
theorem n3_dvd_iff {k m n : ℕ} (hmn : m ≤ n) :
    (3 : ℤ) ^ k ∣ n3Resid m - n3Resid n ↔
      k ≤ 2 * m + 1 ∨ m = n
```

*Runners-up: `n2Resid_diff` (0.0), `n1Resid_diff` (0.0)*

*If this row describes a definition rather than a theorem: `balWidth`, `n2Resid`*

## 5. `BTA-x3-n0-sign`

**Row.** N0(p)≡N0(-p) iff 3^k | N0(p)

**Candidate.** `deficit_unexhausted_iff` &mdash; kernel-checked, `BTCalculus/CubicN0Reduction.lean:82`

No docstring; the statement itself:

```lean
theorem deficit_unexhausted_iff {k r : Nat} (_hr : r + 1 ≤ k) :
    k - 1 - r ≤ 3 * r ↔ k ≤ 4 * r + 1
```

*Runners-up: `DZ_mul_three` (0.0), `pow3_mul_cube` (0.0)*

## 6. `BTA-x3-Q-eq`

**Row.** Q(u)=Q(v) iff 3^{t+K} divides u^3-v^3-Δbal_t

**Candidate.** `q_eq_iff_of_same_bal` &mdash; kernel-checked, `BTCalculus/MismatchedCubicQuotient.lean:181`

No docstring; the statement itself:

```lean
theorem q_eq_iff_of_same_bal {t K : Nat} {u v : Int}
    (hbal : balCubic t u = balCubic t v) :
    (3 : Int) ^ K ∣ qCubic t u - qCubic t v ↔
      (3 : Int) ^ (t + K) ∣ u ^ 3 - v ^ 3
```

*Runners-up: `q_eq_iff` (0.333), `q_recon` (0.0)*

*If this row describes a definition rather than a theorem: `balCubic`, `qCubic`*

## 7. `BTA-x3-Q-inv-one`

**Row.** for t>=1, Q(1+3^t b)=Q(1+3^t c) iff 3^{K-1} divides b-c

**Candidate.** `three_pow_dvd_mul_iff` &mdash; kernel-checked, `BTCalculus/MismatchedCubicInvariant.lean:95`

No docstring; the statement itself:

```lean
lemma three_pow_dvd_mul_iff :
    ∀ (n : Nat) {x U : Int}, ¬ (3 : Int) ∣ U →
      ((3 : Int) ^ n ∣ x * U ↔ (3 : Int) ^ n ∣ x)
  | 0, x, U, _ => by simp
  | n + 1, x, U, hU => by
```

*Runners-up: `iterDZ_one` (0.0), `qCubic_one` (0.0)*

## 8. `BTL-block-shift`

**Row.** block shift law: for a word w of length j the section operators send the state (3^j d, 3^{j+i}) to (d + 3^i packWord(w), 3^{j+i}), every such word survives, and at i = 0, j = e the 3^e words of length e reach exactly the states d + t for t in the balanced window W_e = [-(3^e-1)/2, (3^e-1)/2]; the shift is the balanced value packWord(w) an

**Candidate.** `residualAlong_linState_pow` &mdash; kernel-checked, `BTCalculus/PadicLiftingState.lean:302`

> **Target 4.** The block shift law. A singular branch with derivative valuation at least `w.length` is fully ternary along `w`, and the state it reaches is shifted by the *balanced value* of the word, scaled by the excess `3 ^ i`: 𝔇_w (3^j d + 3^(j+i) x) = (d + 3^i · packWord w) + 3^(j+i) x, j = |w|. At `i = 0` this is the leaf law: the `3 ^ e` words of length `e` reach the states `d + packWord w`, and `packWord` is injective on words of a fixed length, so those shifts run over a complete residue system modulo `3 ^ e`. That is what makes the shifted family separate residues; note the shift is the balanced value of the word and not its digit sum.

*Runners-up: `outputAlong_linState_pow` (0.109), `linState_root_iff` (0.083)*

*If this row describes a definition rather than a theorem: `linState`, `henselTrit`*

## 9. `BTC-op-fragment-nd-nf`

**Row.** the operator-fragment tree TRS {D, I_a, S, N} including N(D(x))→D(N(x)) is terminating and locally confluent; every term has a unique syntactic normal form

**Candidate.** `unique_normal_form` &mdash; kernel-checked, `BTCalculus/OpFragNewman.lean:381`

> Unique syntactic normal form of an operator-fragment term.

*Runners-up: `locally_confluent` (0.176), `isNF_normal` (0.077)*

## 10. `BTC-word-simp-nf`

**Row.** the simplifying-only fragment of WORD_REWRITE_RULES (the sixteen rules with simplifying=True: cancellations, the W/K3 stock, and I0→S) is terminating and locally confluent; every word has a unique syntactic normal form

**Candidate.** `unique_normal_form` &mdash; kernel-checked, `BTCalculus/WordSimpNewman.lean:330`

> Unique syntactic normal form of a simplifying-fragment word. Semantic canonicity of that irreducible is not claimed.

*Runners-up: `locally_confluent` (0.091), `normal_rtc` (0.059)*

## 11. `BTM-x3-depth`

**Row.** for every balanced-Monna endpoint pair u=zeta+2*3^n, v=zeta-2*3^n one has u^3-v^3=4*3^n(3 zeta^2+4*3^{2n}) and therefore t=v_3(u^3-v^3)=n+min(1+2 v_3(zeta), 2n), or t=3n when zeta=0; the two arguments of the minimum have opposite parity whenever zeta is nonzero

**Candidate.** `monnaEndpoint_val_parity` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:93`

> The two arguments of the depth minimum have opposite parity when `ζ ≠ 0`.

*Runners-up: `monnaEndpoint_cube_val_of_ne` (0.143), `monnaEndpoint_factor_ne` (0.133)*

*If this row describes a definition rather than a theorem: `monnaEndpointU`, `monnaEndpointV`*

## 12. `BTC-push-in-S-peak`

**Row.** the named carry-free push-in system (unary D(S(t))→t plus S(Add(t,u))→Add(S(t),S(u)) and congruence, no D-through-Add) is not locally confluent: D(S(Add(X,Y))) has two distinct irreducibles Add(X,Y) and D(Add(S(X),S(Y))); both evaluate to X+Y

**Candidate.** `pushIn_not_locally_confluent` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:212`

> The named carry-free push-in system is not locally confluent: `D(S(X+Y))` has two distinct irreducibles.

*Runners-up: `D_add_unsound` (0.235), `add_requires_carry_state` (0.192)*

*If this row describes a definition rather than a theorem: `pushInPeak`, `DLocal`*

## 13. `BTC-add-requires-carry-state`

**Row.** the packaged Add boundary combines three exact statements: D(x+y) is not D-local, same-sign I_a is not a constructor identity, and the named carry-free S-through-Add push-in extension fails local confluence

**Candidate.** `add_requires_carry_state` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:237`

> Packaged Add boundary: `D ∘ Add` is not D-local, same-sign `I_a` is not a constructor identity, and the named carry-free push-in extension fails local confluence.

*Runners-up: `D_add_unsound` (0.19), `pushIn_not_locally_confluent` (0.167)*

*If this row describes a definition rather than a theorem: `exactTriple`, `DLocal`*

## 14. `OST-np-energy-ext-interval`

**Row.** for Γ_NP, the set of integer controls w such that E_{n-1}(T_w s) lies in a fixed integer interval [lo, hi] is consecutive: if w1 and w2 satisfy the bounds and w1 ≤ w ≤ w2 then w does too; this is energy_step plus q>0, not a bound on L_0

**Candidate.** `energy_control_interval` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:202`

> The set of integer controls `w` with `E_{n-1}(T_w s)` in a fixed interval `[lo, hi]` is consecutive. This is `energy_step` plus `q > 0`, not a bound on `L₀`.

*Runners-up: `energy_step_state` (0.133), `adjointDet_eq` (0.095)*

*If this row describes a definition rather than a theorem: `energy`, `applyA`*

## 15. `OST-np-energy-homogeneous`

**Row.** for Γ_NP, homogeneous residual motion is energy-neutral in the sliding index: E_n(A^k s) = E_{n+k}(s), equivalently energy_telescope on the zero word; this is not a bound on L_0

**Candidate.** `energy_homogeneous` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:236`

> Homogeneous motion `A^k = T_0^k` preserves energy in the sliding index: `E_n(A^k s) = E_{n+k}(s)`. This is `energy_telescope` on the zero word, not a bound on `L₀`.

*Runners-up: `energy_zero` (0.167), `recurrence_word_zero` (0.154)*

*If this row describes a definition rather than a theorem: `applyA`, `energy`*

## 16. `OST-np-adjoint-window-det`

**Row.** for Γ_NP and n≥2, the determinant of consecutive adjoints (u_n, u_{n-1}, u_{n-2}) equals 3^{n-2}, so neighboring energies invert s over Q; this is not a bound on L_0

**Candidate.** `adjointDet_eq` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:335`

> Consecutive adjoints are independent: `det = 3^{n-2}` for `n ≥ 2`. Neighboring energies invert `s` over `ℚ`. Not a bound on `L₀`.

*Runners-up: `energy_control_interval` (0.118), `reset_pow_then_hub` (0.083)*

*If this row describes a definition rather than a theorem: `tripleDet`, `qShift`*

## 17. `OST-np-impulse-place`

**Row.** for Γ_NP, the origin impulse A^r e3 equals (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r) with q_j=0 for j<0; this is the place-value dictionary for origin_particular, not a bound on L_0

**Candidate.** `iterateA_e3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:776`

> `A^r e₃ = (3 q_{r-1}, 3 q_{r-2}+q_{r-1}, q_r)`. KNOWN place-value dictionary for `origin_particular`, not `L₀`.

*Runners-up: `particular_s3` (0.182), `reset_pow_then_hub` (0.182)*

*If this row describes a definition rather than a theorem: `impulsePlace`, `particularSum`*

## 18. `OST-np-particular-s3`

**Row.** for Γ_NP, from the origin the third coordinate of the control particular equals minus the MSD consumed valuation: (particularSum ws)_3 = -consumedSum |ws| ws, so val(B)=0 iff c_B lies on F={s_3=0}; this is energy_telescope at n=0, not a bound on L_0

**Candidate.** `particular_s3` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:556`

> From the origin, `(c_B)₃ = -val(B)`. KNOWN energy at `n=0`, not `L₀`.

*Runners-up: `fold_s3` (0.136), `energy_homogeneous` (0.125)*

*If this row describes a definition rather than a theorem: `particularSum`, `consumedSum`*

## 19. `OST-np-reset-pow-then-hub`

**Row.** for Γ_NP, the MSD word (B*)^k · (1,-2) has origin particular equal to the hub (-3,-1,0); this is the reset identity plus hub_nonreset, not a bound on L_0

**Candidate.** `reset_pow_then_hub` &mdash; kernel-checked, `Problems/Ostrowski/NP/Energy.lean:727`

> `(B*)^k · (1,-2)` has particular the hub. Not a bound on `L₀`.

*Statement names: `hub_nonreset`*

*Runners-up: `reset_prefix` (0.176), `hub_nonreset` (0.154)*

*If this row describes a definition rather than a theorem: `recurrenceWord`, `particularSum`*

## 20. `OST-np-unique-predecessor`

**Row.** for Γ_NP, if T_w(s)=t then s equals the integer reverse (t2-t1/3, t3+w-2 t1/3, t1/3); on F this is (b-a/3, w-2a/3, a/3). This is inversion of step, not a bound on L_0

**Candidate.** `predecessor_on_F` &mdash; kernel-checked, `Problems/Ostrowski/NP/KernelFamily.lean:87`

> On `F`, the unique integer predecessor is `(b - a/3, w - 2(a/3), a/3)`. KNOWN inversion of `step`, not `L₀`.

*Runners-up: `step_s3` (0.167), `qPrev_zero` (0.0)*

*If this row describes a definition rather than a theorem: `explicitPredecessor`, `kernelPredFst`*

## 21. `BTN-carry-gain-3`

**Row.** The synthetic map T_3(c,d)=3 DZ(c+2d) satisfies c_n=3n along the all-+1 word, so the residual set is unbounded. This is not value-preserving normalization.

**Candidate.** `carryGain3_eq` &mdash; kernel-checked, `Problems/BalancedTernary/FiniteStateDynamics.lean:143`

> `carryGain3 n = 3n` along the all-`+1` word.

*Runners-up: `carryGain3_unbounded` (0.071), `isTrit_natAbs` (0.062)*

*If this row describes a definition rather than a theorem: `doubledNext`, `doubledOut`*

## 22. `C-no-uniform-L-descent`

**Row.** For every L≥1, n=2^L-1 realises L odd shortcut steps and C^L(n)=3^L-1>n. No residual n mod 2^L with blocks of length at most L certifies strict descent.

**Candidate.** `shortcutC_no_uniform_L_descent` &mdash; kernel-checked, `Problems/Collatz/Shortcut.lean:110`

> For every ``L ≥ 1``, ``n = 2^L - 1`` realises ``L`` odd steps and expands.

*Runners-up: `shortcutC_odd` (0.167), `shortcutC_odd_increases` (0.154)*

*If this row describes a definition rather than a theorem: `shortcutC`, `shortcutCIter`*

## 23. `BTN-sdr-escape-general`

**Row.** If λ≥3 and |u|≥2 then the constant-control orbit of F_{λ,U} from 0 is unbounded: at λ=3 one has s'=s+u-lsd(s+u) so each step moves by at least 1; at λ≥4 the step is strictly expanding on the matching ray.

**Candidate.** `gain3_control2_unbounded` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:105`

No docstring; the statement itself:

```lean
theorem gain3_control2_unbounded (B : ℕ) :
    ∃ n : ℕ, B < (carryGain3 n).natAbs
```

*Runners-up: `finite_residual_condition` (0.083), `lsdZ_le_one` (0.083)*

*If this row describes a definition rather than a theorem: `signedNext`, `signedOut`*

## 24. `BTN-sdr-lambda2-radius`

**Row.** For λ=2 and |u|≤m, if |s|≤2 m.pred then |2 D(s+u)|≤2 m.pred. This is the sharp invariant radius 2(m-1)_+.

**Candidate.** `lambda2_sharp_box` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidual.lean:81`

> Sharp ``λ=2`` invariant radius ``2 m.pred``.

*Runners-up: `lambda2_box_invariant` (0.222), `lambda1_lyapunov` (0.1)*

*If this row describes a definition rather than a theorem: `signedNext`, `signedOut`*

## 25. `BTN-sdrg-lambda1-interval`

**Row.** For λ=1 and U_m, every integer s with |s|≤⌊m/2⌋ is reached from 0 by an admissible word. The explicit positive word is u=2,4,...,2n.

**Candidate.** `lambda1_interval_reachable` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualGeometry.lean:80`

> Every nonnegative point of the ``λ=1`` box is reached by an admissible word.

*Runners-up: `lambda1Word_fold` (0.125), `lambda1Word_abs_le` (0.125)*

*If this row describes a definition rather than a theorem: `lambda1Word`, `lambda2Word`*

## 26. `BTN-mr-product-closure`

**Row.** For trit pairs (d1,d2) and any gain λ, λ·D(0+d1 d2)=0. Origin-reachable residual of two-trit product forcing is {0}, matching F_{λ,U_1}.

**Candidate.** `product_residual_closure` &mdash; kernel-checked, `Problems/BalancedTernary/MultiplicativeResidual.lean:44`

> Origin-reachable residual of two-trit product forcing is ``{0}``.

*Runners-up: `product_origin` (0.222), `product3_origin` (0.222)*

*If this row describes a definition rather than a theorem: `doubledProductNext`, `productRaw`*

## 27. `J-near-tight-scale-bounds`

**Row.** The local Juggler remainder satisfies 0≤ρ<2T+1, hence η=ρ/T^2 < 2/T + 1/T^2 and 1+η < ((T+1)/T)^2. For the mixed itinerary OOE, 1+q = (1+η0)^3 (1+η1)^2 (1+η2)^4, and 1+q is strictly below the successor-ratio product ((T0+1)/T0)^6 ((T1+1)/T1)^4 ((T2+1)/T2)^8. The same bound at a successor start y depends only on the itinerary of y.

**Candidate.** `large_lambda_successor_q_bound` &mdash; kernel-checked, `Problems/Juggler/NearTightScale.lean:201`

> The `OOE` successor bound depends only on the itinerary of `y`. A large-`λ` predecessor enters only by making `y` large.

*Runners-up: `ooe_one_plus_slack_lt_succ_ratio` (0.15), `even_remainder_bound` (0.118)*

## 28. `J-odd-remainder-even`

**Row.** If x is odd, T(x)=y is odd, and ρ=x³-y² is the local odd remainder, then ρ is even. This is the opposite parity of peakOddDefect_odd, which requires an even maximum.

**Candidate.** `odd_remainder_even` &mdash; kernel-checked, `Problems/Juggler/SequentialMordell.lean:63`

> On an odd-to-odd step the remainder is even. The peak law `peakOddDefect_odd` is the opposite parity, and needs an even max.

*Runners-up: `peak_needs_even_max` (0.278), `two_odd_steps_not_peak_shape` (0.167)*

*If this row describes a definition rather than a theorem: `sequentialDefect`, `oddMordellStep`*

## 29. `J-fixed-itinerary-image-monotone`

**Row.** If n and m realize the same finite Juggler word w and n ≤ m, then the image of n after w is at most the image of m after w.

**Candidate.** `image_word` &mdash; kernel-checked, `Problems/Juggler/Itinerary.lean:112`

No docstring; the statement itself:

```lean
theorem image_word (n k : ℕ) : image n (itinerary n k) = floorPower^[k] n
```

*Runners-up: `image_eq_iterate` (0.125), `image_append` (0.125)*

*If this row describes a definition rather than a theorem: `image`, `follows`*

## 30. `J-finite-progress-boundary`

**Row.** Universal FiniteProgress for starts above one implies universal reachability of one. Every even start n ≥ 2 and every odd start n ≥ 2 whose first image is even has FiniteProgress; consequently, any start without FiniteProgress is odd and has an odd first image. This isolates the automatic odd-to-odd frontier without proving universal prog

**Candidate.** `odd_even_finiteProgress` &mdash; kernel-checked, `Problems/Juggler/Progress.lean:78`

> Odd `n ≥ 2` whose first image is even has finite progress: `OE`.

*Runners-up: `finiteProgress_of_imageLt` (0.208), `finiteProgress_of_not_odd_odd` (0.2)*

*If this row describes a definition rather than a theorem: `FiniteProgress`*

## 31. `J-first-even-overshoots`

**Row.** On a MinimalNonTerm or CycleMin start, the first even residual always overshoots: T(O^a E)(n) > n and the even residual sits at or above (n+1)^2. The return-to-n cell of the first-even dichotomy is an even-count-1 cycle itinerary, now excluded by no_cycle_itinerary_even_count_le_three. Lean theorems minimal_first_even_overshoots and cycle

**Candidate.** `minimal_first_even_overshoots` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:649`

> On a `MinimalNonTerm` start the first even residual always overshoots. The return cell is an even-count-1 cycle itinerary. This is not a halt theorem.

*Statement names: `minimal_first_even_overshoots`, `cycleMin_first_even_overshoots`*

*Runners-up: `cycleMin_first_even_overshoots` (0.3), `cycleMin_max_ge_succ_sq` (0.278)*

*If this row describes a definition rather than a theorem: `evenCount`*

## 32. `J-cyclemax-succ-sq`

**Row.** On a CycleMin start n ≥ 2 the cycle maximum satisfies (n+1)^2 ≤ M. Equivalently, on a CycleMax the rotated minimum m satisfies (m+1)^2 ≤ M, so T(M) > m. The first-cell family m^2 < M < (m+1)^2 is impossible. cycle_distinguished_order_succ_sq is the distinguished-order package with that scale. Corollary of cycleMin_first_even_overshoots: t

**Candidate.** `cycleMin_max_ge_succ_sq` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:734`

> On a cycle minimum the maximum sits at or above `(n+1)^2`. The first even residual already overshoots, so the first-cell family `n^2 < M < (n+1)^2` is impossible. Not a halt theorem.

*Statement names: `cycle_distinguished_order_succ_sq`, `cycleMin_first_even_overshoots`, `cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`, `cycleMax_landing_gt_min`, `cycleMax_exists_min_succ_sq`*

*Runners-up: `cycleMax_min_succ_sq_le` (0.222), `minimal_first_even_overshoots` (0.214)*

*If this row describes a definition rather than a theorem: `evenCount`*

## 33. `J-cyclemin-transport-oo`

**Row.** On a CycleMin, after the first O^a E with a ≥ 2, an immediate odd run of length at least two overshoots the landing y = T_{O^a E}(n) > n: the next two-odd residual is at least (y+1)^2, hence at least (n+2)^2. Lean: cycleMin_transport_second_oo, cycleMin_transport_second_oo_ge in CycleMinObstruction.lean. The second residual lies outside t

**Candidate.** `cycleMin_transport_second_oo` &mdash; kernel-checked, `Problems/Juggler/CycleMinObstruction.lean:60`

> After the first `O^a E` on a `CycleMin`, an immediate odd run of length at least two overshoots the landing `y`: the next two-odd residual is at least `(y+1)^2`.

*Statement names: `cycleMin_transport_second_oo`, `cycleMin_transport_second_oo_ge`*

*Runners-up: `cycleMin_transport_second_oo_ge` (0.27), `follows_replicate_odd_of_le` (0.029)*

## 34. `J-exponent-expanding-append`

**Row.** If u and v are expanding itineraries (2^{|u|} < 3^{#O(u)} and 2^{|v|} < 3^{#O(v)}), then u ++ v is expanding: 2^{|u|+|v|} = 2^{|u|} 2^{|v|} < 3^{#O(u)} 3^{#O(v)}. A concatenation of expanding residual blocks is never an exponent-gap certificate. This is not a finite PE-run bound and not a halt theorem.

**Candidate.** `exponentExpanding_append` &mdash; kernel-checked, `Problems/Juggler/ItineraryStats.lean:115`

> Expanding itineraries are closed under concatenation. A concatenation of expanding residual blocks is never an exponent-gap certificate.

*Runners-up: `exponentExpanding_not_gap` (0.231), `odd_run_even_residual` (0.133)*

*If this row describes a definition rather than a theorem: `exponentGap`, `exponentExpanding`*

## 35. `J-minimal-prefix-noncontracting`

**Row.** If MinimalNonTerm n and n follows w, then w is not an exponent-gap itinerary, and every prefix of w is noncontracting. Contrapositive of power_bound_contracts plus minimal_nonterm_no_descent. Concatenating expanding residual blocks therefore cannot create an exponent certificate on a CE. This is not a proof that escape is impossible and n

**Candidate.** `minimal_nonterm_prefix_noncontracting` &mdash; kernel-checked, `Problems/Juggler/Escape.lean:245`

> Every realized prefix of a CE is prefix-noncontracting. Concatenating expanding residual blocks therefore cannot create an exponent certificate on a CE. This is not a halt theorem.

*Runners-up: `minimal_nonterm_not_exponentGap` (0.29), `follows_ooeooeo_image_lt_sq` (0.097)*

*If this row describes a definition rather than a theorem: `itineraryOOEOOEO`, `itineraryOOEOOEOO`*

## 36. `J-ce-third-residual-preimages`

**Row.** If n ≥ 2 follows OOEOOEOO, then T_OOEOOEOO(n) < n^3 because x^{256} ≤ n^{729} forbids n^3 ≤ x (768 > 729). If n follows OOEOOEOOE, then T_OOEOOEOOE(n) < n^2 because y^{512} ≤ n^{729} forbids n^2 ≤ y (1024 > 729). A CE that follows OOEOOE follows OOEOOEOO. On MinimalNonTerm a completed third OOE cannot land even: an even landing below n^2 

**Candidate.** `minimal_ooeooeooe_not_even_landing` &mdash; kernel-checked, `Problems/Juggler/Escape.lean:309`

> On a CE, a completed third `OOE` cannot land even: the landing is below `n^2`, so an even landing is descent. This is not a PE theorem.

*Runners-up: `minimal_ooeooeooeoe_not_even_landing` (0.32), `minimal_ooeooeooeoeo_not_even` (0.222)*

*If this row describes a definition rather than a theorem: `itineraryOOEOOEOO`, `itineraryOOEOOEOOE`*

## 37. `J-envelope-lt-pow`

**Row.** If n ≥ 2, A > 0, x^A ≤ n^B, and B < k·A, then x < n^k. EnvelopeState n x packages the free inequality x^A ≤ n^B, with even (A,B)→(2A,B) and odd (A,B)→(2A,3B). PowerBound is the special case A=2^|w|, B=3^{oddCount w}. A realized itinerary with 3^{oddCount w} < k·2^{|w|} therefore has T_w(n) < n^k. power_bound_contracts is the k=1 case. Esc

**Candidate.** `power_bound_lt_pow` &mdash; kernel-checked, `Problems/Juggler/Envelope.lean:312`

> Word-stat form: `3^{oddCount w} < k · 2^{|w|}` yields `T_w(n) < n^k`. Implemented by `EnvelopeState.of_follows`. `power_bound_contracts` is the `k = 1` case.

*Statement names: `power_bound_contracts`*

*Runners-up: `even_itinerary_contracts` (0.143), `pow_sq_le_cube` (0.129)*

*If this row describes a definition rather than a theorem: `EnvelopeState.of_powerBound`, `EnvelopeState.map_itinerary`*

## 38. `J-cube-odd-even-reset`

**Row.** If n ≥ 2 and n^2 ≤ x < n^3 with x odd, then n^3 ≤ T(x) < n^5 and T(x)^2 < n^9. If T(x) is even, the first return satisfies n ≤ T^2(x) < x < n^3 and T^2(x)^4 < n^9. If T(x) is odd, then x < T^2(x) and n^4 ≤ T^2(x). An even reset that is itself even and already below n^2 is FiniteProgress; on MinimalNonTerm that case is impossible. This is 

**Candidate.** `aboveAnchor_not_odd_even` &mdash; kernel-checked, `Problems/Juggler/MinimumRelative.lean:103`

> An `OE` start cannot stay at or above the anchor: the first even residual is below `n^2`.

*Runners-up: `aboveAnchor_isolatedOddSurvival` (0.037), `even_ge_sq_of_aboveAnchor` (0.032)*

*If this row describes a definition rather than a theorem: `AboveAnchor`*

## 39. `J-cyclemin-defect-finance-kill`

**Row.** The defect-sum finance inequality (the certified identity of Paper A Theorem 4.6, previously human) and the walk-charge kill criterion (Theorem 5.9 mechanism), Lean end to end (DefectFinance.lean). Finance: on a CycleMin cycle with minimum n ≥ 400, 1 − 2^L/3^o ≤ (6/5)·Σ_k 1/(x_k·log x_k) (cycleMin_defect_finance). Ingredients all Lean: pe

**Candidate.** `cycleMin_hug_kill_criterion` &mdash; kernel-checked, `Problems/Juggler/DefectFinance.lean:439`

> **The walk-charge kill criterion** (Paper A Theorem 5.9 mechanism, Lean form): every minimum-based cycle at `n ≥ 400` with positive reduced log-base `ν = log n − D` must satisfy `1 − 2^L/3^o ≤ (6/5) · Σ_k g(hugWeight k)` with the charge evaluated at the reduced base. The kill tables verify the numeric failure of this inequality per surviving length; that evaluation stays verified computation, the implication is Lean.

*Statement names: `cycleMin_defect_finance`, `neg_log_one_sub_le_sixth`, `log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`, `log_floorPower_even_le`, `log_floorPower_odd_le`, `cycleMin_log_le_weight`, `cycleMin_charge_prefix`, `cycleMin_hug_kill_criterion`*

*Runners-up: `cycleMin_defect_finance` (0.134), `log_floorPower_even_ge_sub` (0.11)*

## 40. `J-loglog-clock-band-word-forced-lean`

**Row.** Inside the hug band the parity letter is forced. band_step_forced_odd: from u < 1 a step staying in [0, 1 + alphaClock) must be the odd one, v = u + alphaClock (the even step goes negative). band_step_forced_even: from 1 <= u it must be the even one, v = u - 1 (the odd step exceeds the band). band_successor_unique: a band-confined walk ha

**Candidate.** `band_successor_unique` &mdash; kernel-checked, `Problems/Juggler/LogLogClock.lean:152`

> **The band walk is the rotation by `alphaClock`.** A walk confined to the hug band has a single admissible successor at every point, given by the lift of the rotation: `u + alphaClock` below `1`, `u - 1` above. So the parity word of a band-confined orbit is determined by nothing but the starting walk — it is the mechanical word of the rotation, the hug itinerary.

*Statement names: `band_step_forced_odd`, `band_step_forced_even`, `band_successor_unique`*

*Runners-up: `band_step_forced_odd` (0.263), `band_step_forced_even` (0.263)*

*If this row describes a definition rather than a theorem: `WalkStep`*

