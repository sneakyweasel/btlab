# Declaration review queue

Rows where one candidate leads its file clearly.  Each entry is the ledger row's own
statement beside the candidate's docstring; the question is only whether they say the
same thing.  Measured against all 115 single-declaration rows the scorer gets
41 of the 48 it fires on right, 85% precise, so roughly one in
7 below is wrong.
54 rows below, of 131 unresolved.


Two failure modes are not scored at all, and both record a part as the whole.

The row may be broader than the candidate: `BTC-select3` reads "select3 represents
every Trit->Z map; abs/min/max" -- four theorems, of which `select3_represents` is
one.  If a row says "and", ";" or lists several claims, it belongs in neither column.

Or the candidate may be narrower than the row, with nothing in the prose to say so.
`BTN-sdrg-lambda1-interval` claims every integer with |s| <= m/2 is reachable, and
`lambda1_interval_reachable` reads "every nonnegative point" -- true, and half of it;
its `n : ℕ` is the tell, and a sibling proves the rest.  That is why the statement is
printed below every candidate, docstring or not.

Jev (jev-1.13.0, last asked 2026-09-21) answered 129 of
the unresolved rows: 68 picks and 45 "none of these".
26 of the picks are the scorer's own first candidate, and
39 are at or above 0.7 confidence.  A confident pick lists
a row here whatever the scorer thought, and every entry shows Jev's answer beside
the scorer's.  Jev returns a probability, not a reading: a second opinion for the
reviewer, never a ledger write.

Measured on 40 resolved rows on 2026-09-21 (jev-1.13.0): the
recorded declaration first 27 times, in its top three 38 times,
right 24 of 29 times at or above 0.7
confidence.  The scorer's first candidate was right 23 times on the
same rows.

Answer by adding `decl` and `lean_trust` to the row in `docs/theory/theorem_ledger.json`.

## 1. `J-paper-b-lemma-5-1-minimal-certificates`

**Row.** Paper B Lemma 5.1: the contracting words of length at most five with no proper nonempty contracting prefix are exactly E, OE, OOEE, OOOEE, and OOEOE. Their formal cylinder measures sum to 1/2+1/4+1/16+1/32+1/32=7/8 (and the four-step and 27/32 subfamily sums likewise). Lean: Problems.Juggler.PaperBCertificates.lemma51 and certificate_meas

**Candidate.** `lemma51` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificates.lean:180`

> **Lemma 5.1.** The minimal certificates of length at most five are exactly `E`, `OE`, `OOEE`, `OOOEE`, and `OOEOE`.

```lean
theorem lemma51 {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length ≤ 5) :
    w = certE ∨ w = certOE ∨ w = certOOEE ∨ w = certOOOEE ∨ w = certOOEOE
```

**Jev.** picks `lemma51_complete` at 0.93, not the scorer's candidate.

**Jev's candidate.** `lemma51_complete` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificates.lean:202`

> The five named words are indeed the complete list through length five.

```lean
theorem lemma51_complete :
    (∀ w, IsMinimalCertificate w → w.length ≤ 5 →
      w = certE ∨ w = certOE ∨ w = certOOEE ∨ w = certOOOEE ∨ w = certOOEOE) ∧
    IsMinimalCertificate certE ∧ IsMinimalCertificate certOE ∧
    IsMinimalCertificate certOOEE ∧ IsMinimalCertificate certOOOEE ∧
    IsMinimalCertificate certOOEOE ∧
    (1 : ℚ) / 2 + 1 / 4 + 1 / 16 + 1 / 32 + 1 / 32 = 7 / 8
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `certificate_measures_sum`, `four_step_measures_sum`, `twenty_seven_thirty_two_sum`*

*Runners-up: `certificate_measures_sum` (0.189), `four_step_measures_sum` (0.108)*

*If this row describes a definition rather than a theorem: `IsMinimalCertificate`, `certE`*

## 2. `J-paper-b-certificate-length-window`

**Row.** Paper B Lemma 5.1 holds for every length, not only the printed five. Write CertWindow L o for 2^(L-1) <= 3^o < 2^L. (i) certWindow_unique: at most one o satisfies it, since consecutive powers of two differ by a factor 2 and 3 > 2. (ii) minimalCert_concat_even: a minimal certificate's last letter is E, because an odd one would need 3 * 3^o

**Candidate.** `blockWord_isMinimalCertificate` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificateLengths.lean:185`

> **The window is attained.** When some power of three lies in `[2 ^ (L-1), 2 ^ L)`, the word `O^o E^(L-o)` is a minimal certificate: every proper prefix either is all odd (where `3 ^ k > 2 ^ k`) or is `O^o E^j` with `j < L - o`, where the window's lower bound `2 ^ (L-1) ≤ 3 ^ o` is exactly what stops it contracting early.

```lean
theorem blockWord_isMinimalCertificate {L o : ℕ} (hL : 0 < L) (ho : o ≤ L)
    (hwin : CertWindow L o) : IsMinimalCertificate (blockWord L o)
```

**Jev.** picks `minimalCert_exists_iff` at 0.86, not the scorer's candidate.

**Jev's candidate.** `minimalCert_exists_iff` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificateLengths.lean:228`

> **Lemma 5.1 for every length.** A minimal certificate of length `L ≥ 1` exists exactly when some power of three lies in `[2 ^ (L - 1), 2 ^ L)`. The manuscript's list is the case `L ≤ 5`.

```lean
theorem minimalCert_exists_iff {L : ℕ} (hL : 0 < L) :
    (∃ w : List Branch, IsMinimalCertificate w ∧ w.length = L) ↔ ∃ o, CertWindow L o
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `certWindow_unique`, `minimalCert_concat_even`, `minimalCert_window`, `blockWord_isMinimalCertificate`, `minimalCert_exists_iff`, `window_empty_three`*

*Runners-up: `minimalCert_exists_iff_natLog` (0.151), `minimalCert_concat_even` (0.135)*

*If this row describes a definition rather than a theorem: `CertWindow`, `blockWord`*

## 3. `J-paper-b-survivor-certificate-recursion`

**Row.** The survivor count and the minimal-certificate count of Paper B are one recursion. Let N_d = neverNegCount d count the length-d parity words no prefix of which contracts and M_d = minimalCertCount d the minimal certificates of length d. (i) neverNegCount_add_minimalCertCount: N_(d+1) + M_(d+1) = 2 N_d, by one extension step -- extending a

**Candidate.** `neverNegCount_succ_sub_onBarrier` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificateRecursion.lean:272`

> **`N_(d+1) = 2 N_d - b_d M_d`, in the shape the boundary-mass row states it.** The recursion doubles exactly when `onBarrierCount d = 0`, and those lengths have a closed form: `M_d = 0` iff `d` lies in OEIS A054414, `1 + floor (n / (1 - log 2 / log 3))`, apart from `d = 1`, where `E` contracts at once; `M_d /= 0` iff `d` lies in A020914, `floor (n * log 2 3) + 1`, the laboratory's own distinguished length. The two partition the positive integers, so the plateaus of `density_flat_of_window_empty` below are a Beatty complement rather than a list. Checked to `d = 200` in `research.juggler_sequence.oeis_neighbourhood`; A054414 is the only one of the four sequences around this recursion that the laboratory had not already named.

```lean
theorem neverNegCount_succ_sub_onBarrier (d : ℕ) :
    neverNegCount (d + 1) + onBarrierCount d = 2 * neverNegCount d
```

**Jev.** picks `neverNegCount_add_minimalCertCount` at 0.86, not the scorer's candidate.

**Jev's candidate.** `neverNegCount_add_minimalCertCount` &mdash; kernel-checked, `Problems/Juggler/PaperBCertificateRecursion.lean:171`

> **`N_{d+1} + M_{d+1} = 2 N_d`.** Each survivor of length `d` has two extensions, and each extension either survives or contracts for the first time.

```lean
theorem neverNegCount_add_minimalCertCount (d : ℕ) :
    neverNegCount (d + 1) + minimalCertCount (d + 1) = 2 * neverNegCount d
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `neverNegCount_add_minimalCertCount`, `prefixNoncontracting_concat`, `isMinimalCertificate_concat`, `extensions_eq_survivors_union_certs`, `certifiedWordCount_succ`, `density_succ`, `minimalCertCount_eq_zero_of_window_empty`, `density_flat_of_window_empty`, `density_flat_five_to_six`, `density_flat_eight_to_nine`, `density_flat_ten_to_eleven`, `minimalCertCount_succ`, `minimalCertWords_succ`, `not_exponentGap_concat_odd`*

*Runners-up: `density_succ` (0.132), `neverNegCount_add_minimalCertCount` (0.11)*

*If this row describes a definition rather than a theorem: `onBarrierWords`, `minimalCertCount`*

## 4. `BTC-P-band`

**Row.** P_a ∘ P_b = P_a

**Candidate.** `trit_toInt_is_trit` &mdash; kernel-checked, `BTCalculus/Integral.lean:14`

```lean
theorem trit_toInt_is_trit (a : Trit) :
    a.toInt = -1 ∨ a.toInt = 0 ∨ a.toInt = 1
```

**Jev.** picks `P_left_zero` at 0.86, not the scorer's candidate.

**Jev's candidate.** `P_left_zero` &mdash; kernel-checked, `BTCalculus/Integral.lean:49`

```lean
theorem P_left_zero (a b : Trit) (n : ℤ) : PZ a (PZ b n) = PZ a n
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `IZ_mod` (0.0), `lsdZ_IZ` (0.0)*

*If this row describes a definition rather than a theorem: `IZ`, `PZ`*

## 5. `BTC-select3`

**Row.** select3 represents every Trit→ℤ map; abs/min/max

**Candidate.** `select3_represents` &mdash; kernel-checked, `BTCalculus/Select.lean:33`

> Every function ``Trit → ℤ`` is ``select3`` of its three values.

```lean
theorem select3_represents (f : Trit → ℤ) (c : Trit) :
    f c = select3 c (f Trit.minus) (f Trit.zero) (f Trit.plus)
```

**Jev.** picks `select3_represents` as well, at 0.96.

*Runners-up: `select3_minus` (0.182), `select3_zero` (0.182)*

*If this row describes a definition rather than a theorem: `select3`, `absZ`*

## 6. `BTN-lex`

**Row.** LSD step strictly decreases the abs-lex rank

**Candidate.** `step_lex_zero` &mdash; kernel-checked, `BTCalculus/Normalization.lean:123`

> The step at index `0` strictly decreases the abs-lex rank.

```lean
theorem step_lex_zero {c : ℤ} (cs : List ℤ) (h : ¬ isTrit c) :
    List.Lex (· < ·) (absList (step (c :: cs) 0)) (absList (c :: cs))
```

**Jev.** picks `step_lex_zero` as well, at 0.42.

*Runners-up: `stepZero_lex` (0.417), `lsdZ_natAbs_le_one` (0.25)*

*If this row describes a definition rather than a theorem: `stepZero`, `absList`*

## 7. `BTA-equiv`

**Row.** finite-horizon equiv_k is an equivalence; recursive iff output words

**Candidate.** `equivK_succ_iff` &mdash; kernel-checked, `BTCalculus/Residual.lean:66`

```lean
theorem equivK_succ_iff (k : ℕ) (f g : ℤ[X]) :
    equivK (k + 1) f g ↔
      ∀ a : ℤ, isTrit a →
        lsdZ (eval a f) = lsdZ (eval a g) ∧
          equivK k (sectionDeriv a f) (sectionDeriv a g)
```

**Jev.** picks `equivK_iff_outputs` at 0.71, not the scorer's candidate.

**Jev's candidate.** `equivK_iff_outputs` &mdash; kernel-checked, `BTCalculus/Residual.lean:79`

```lean
theorem equivK_iff_outputs :
    ∀ (k : ℕ) (f g : ℤ[X]),
      equivK k f g ↔
        ∀ w : List ℤ, w.length = k → isTritList w →
          outputAlong w f = outputAlong w g
  | 0, _f, _g => by
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `equivK_iff_outputs` (0.222), `equivK_zero` (0.111)*

*If this row describes a definition rather than a theorem: `equivK`, `isTritList`*

## 8. `BTA-x2-quad-form`

**Row.** residual of x^2 along w is 3^|w| x^2 + 2 p(w) x + DZ^|w|(p(w)^2)

**Candidate.** `residualAlong_family` &mdash; kernel-checked, `BTCalculus/Quadratic.lean:355`

```lean
theorem residualAlong_family (m : ℕ) (p : ℤ) :
    ∀ {w : List ℤ}, isTritList w →
      residualAlong w (quad ((3 : ℤ) ^ m) (2 * p) (iterDZ m (p ^ 2))) =
        quad ((3 : ℤ) ^ (m + w.length))
          (2 * (p + (3 : ℤ) ^ m * packWord w))
          (iterDZ (m + w.length) ((p + (3 : ℤ) ^ m * packWord w) ^ 2))
  | [], _ => by
```

**Jev.** picks `residualAlong_Xsq` at 0.99, not the scorer's candidate.

**Jev's candidate.** `residualAlong_Xsq` &mdash; kernel-checked, `BTCalculus/Quadratic.lean:384`

```lean
theorem residualAlong_Xsq {w : List ℤ} (hw : isTritList w) :
    residualAlong w ((X : ℤ[X]) ^ 2) =
      quad ((3 : ℤ) ^ w.length) (2 * packWord w) (iterDZ w.length (packWord w ^ 2))
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `residualAlong_Xsq` (0.667), `residualAlong_Xsq_injective` (0.5)*

*If this row describes a definition rather than a theorem: `quad`, `packWord`*

## 9. `BTA-quad-mod`

**Row.** degree <= 2 polynomials are equiv_k iff coefficients agree mod 3^k

**Candidate.** `equivK_quad` &mdash; kernel-checked, `BTCalculus/Quadratic.lean:479`

> Finite-horizon equivalence of degree-``≤ 2`` polynomials is coefficient congruence modulo ``3^k``. Canonical probes: ``0^k``, ``10^{k-1}``, ``(-1)0^{k-1}``.

```lean
theorem equivK_quad (k : ℕ) (A B c0 A' B' c0' : ℤ) :
    equivK k (quad A B c0) (quad A' B' c0') ↔
      (3 : ℤ) ^ k ∣ A - A' ∧ (3 : ℤ) ^ k ∣ B - B' ∧ (3 : ℤ) ^ k ∣ c0 - c0'
```

**Jev.** picks `equivK_quad` as well, at 1.0.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `xsq_equivK_iff_eq` (0.167), `integerJet_eq_iff_dvd` (0.1)*

*If this row describes a definition rather than a theorem: `quad`, `packWord`*

## 10. `BTA-x3-newton`

**Row.** Newton coordinates of a cubic and of the residual family of x^3

**Candidate.** `newton_cubicResid` &mdash; kernel-checked, `BTCalculus/CubicResidual.lean:269`

> Newton coordinates of the residual family, written in terms of `m` and `p`.

```lean
theorem newton_cubicResid (m : ℕ) (p : ℤ) :
    newtonCoords ((3 : ℤ) ^ (2 * m)) ((3 : ℤ) ^ (m + 1) * p)
        (3 * p ^ 2) (iterDZ m (p ^ 3)) =
      (iterDZ m (p ^ 3),
        (3 : ℤ) ^ (2 * m) + (3 : ℤ) ^ (m + 1) * p + 3 * p ^ 2,
        2 * (3 : ℤ) ^ (m + 1) * (p + (3 : ℤ) ^ m),
        2 * (3 : ℤ) ^ (2 * m + 1))
```

**Jev.** picks `newton_cubicResid` as well, at 0.71.

*Runners-up: `eval_cubicResid_iter` (0.3), `residualAlong_cubic_family` (0.25)*

*If this row describes a definition rather than a theorem: `cubicResid`, `newtonCoords`*

## 11. `BTA-x3-n2`

**Row.** same-depth N2 is 3^{k-m-1}|(p-q); injective on P_m if 2m+1<=k

**Candidate.** `sameDepth_n2` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:62`

> At one depth, `3^k` divides the `N2` difference exactly when it divides `3^(m+1)(p - q)`.

```lean
theorem sameDepth_n2 (k m : ℕ) (p q : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q ↔
      (3 : ℤ) ^ k ∣ (3 : ℤ) ^ (m + 1) * (p - q)
```

**Jev.** picks `sameDepth_n2_injective` at 0.72, not the scorer's candidate.

**Jev's candidate.** `sameDepth_n2_injective` &mdash; kernel-checked, `BTCalculus/CubicFibres.lean:110`

> `N2` separates points of `P_m` once `2m + 1 <= k`: agreement to that order forces `p = q`. The width bound is what closes it -- the difference cannot reach `3^(k-m-1)`.

```lean
theorem sameDepth_n2_injective {k m : ℕ} {p q : ℤ}
    (hp : balWidth m p) (hq : balWidth m q)
    (hmk : 2 * m + 1 ≤ k)
    (hN2 : (3 : ℤ) ^ k ∣ n2Resid m p - n2Resid m q) :
    p = q
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `sameDepth_n2_of_le` (0.167), `sameDepth_n2_succ` (0.167)*

*If this row describes a definition rather than a theorem: `balWidth`, `n2Resid`*

## 12. `BTA-x3-inter-crit`

**Row.** m=k-2 fibres iff p≡q (mod 3) and 3^{k-1}|(p-q)(p+q+3^{k-2}) and N0 agrees

**Candidate.** `inter_n2_mod` &mdash; kernel-checked, `BTCalculus/CubicIntermediateLayer.lean:33`

```lean
theorem inter_n2_mod {k : ℕ} (hk : 3 ≤ k) (p : ℤ) :
    (3 : ℤ) ^ k ∣ n2Resid (k - 2) p - interN2 k p
```

**Jev.** picks `inter_equiv_iff` at 0.73, not the scorer's candidate.

**Jev's candidate.** `inter_equiv_iff` &mdash; kernel-checked, `BTCalculus/CubicIntermediateLayer.lean:126`

```lean
theorem inter_equiv_iff {k : ℕ} (hk : 2 ≤ k) (p q : ℤ) :
    ((3 : ℤ) ^ k ∣ n2Resid (k - 2) p - n2Resid (k - 2) q) ∧
        ((3 : ℤ) ^ k ∣ n1Resid (k - 2) p - n1Resid (k - 2) q) ∧
          ((3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q) ↔
      ((3 : ℤ) ∣ p - q) ∧
        ((3 : ℤ) ^ (k - 1) ∣ (p - q) * (p + q + (3 : ℤ) ^ (k - 2))) ∧
          ((3 : ℤ) ^ k ∣ n0Resid (k - 2) p - n0Resid (k - 2) q)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `inter_n2_iff` (0.2), `inter_n1_mod` (0.2)*

*If this row describes a definition rather than a theorem: `interN2`, `interN1`*

## 13. `BTA-x3-n0-vis`

**Row.** D^t(u^3) mod 3^k is determined by u mod 3^{max(1,t+k-1)}

**Candidate.** `n0_of_cube_mod` &mdash; kernel-checked, `BTCalculus/CubicN0Reduction.lean:148`

```lean
theorem n0_of_cube_mod {t k : Nat} {u v : Int}
    (h : (3 : Int) ^ (t + k) ∣ u ^ 3 - v ^ 3) :
    (3 : Int) ^ k ∣ n0Resid t u - n0Resid t v
```

**Jev.** picks `n0_visible_mod` at 0.81, not the scorer's candidate.

**Jev's candidate.** `n0_visible_mod` &mdash; kernel-checked, `BTCalculus/CubicN0Reduction.lean:167`

> `N0` modulo a power of three sees only the input modulo a power of three.

```lean
theorem n0_visible_mod {t k s : Nat}
    (hs : t + k - 1 ≤ s) (hs1 : 1 ≤ s) {u v : Int}
    (h : (3 : Int) ^ s ∣ u - v) :
    (3 : Int) ^ k ∣ n0Resid t u - n0Resid t v
```

*Runners-up: `n0_visible_mod` (0.111), `DZ_mul_three` (0.0)*

## 14. `BTA-x3-C-core`

**Row.** 3^r u in P_m iff u in P_{m-r} when r<=m; r>m forces u=0

**Candidate.** `balWidth_pow_iff` &mdash; kernel-checked, `BTCalculus/XCubeStateComplexity.lean:61`

> The two directions together: `balWidth m (3^r u)` iff `balWidth (m-r) u`, for `r <= m`.

```lean
theorem balWidth_pow_iff {m r : Nat} (hr : r ≤ m) (u : Int) :
    balWidth m ((3 : Int) ^ r * u) ↔ balWidth (m - r) u
```

**Jev.** picks `balWidth_pow_iff` as well, at 0.72.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `x3_crossDepth_n3` (0.091), `n1_core_square_iff` (0.067)*

## 15. `BTA-x3-H-A`

**Row.** on the core, N1 agrees iff u^2 agrees modulo 3^{k-2r-1}, and that exponent equals the core width W

**Candidate.** `n1_on_core_mod` &mdash; kernel-checked, `BTCalculus/XCubeStateComplexity.lean:104`

> The core `N1` residual modulo `3^k`, under `r + 1 <= k` and `2r + 2 <= k`.

```lean
theorem n1_on_core_mod {k r : Nat} (hr : r + 1 ≤ k)
    (h2 : 2 * r + 2 ≤ k) (u : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
      (3 : Int) ^ (2 * r + 1) * u ^ 2
```

**Jev.** picks `n1_core_square_iff` at 0.94, not the scorer's candidate.

**Jev's candidate.** `n1_core_square_iff` &mdash; kernel-checked, `BTCalculus/XCubeStateComplexity.lean:265`

> Agreement of the core `N1` residuals modulo `3^k`, stated as a condition on `u` and `v`; the square factorisation is what the depth argument uses.

```lean
theorem n1_core_square_iff {k r : Nat} (h2 : 2 * r + 2 ≤ k) (u v : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
        n1Resid (k - 1 - r) ((3 : Int) ^ r * v) ↔
      (3 : Int) ^ (k - 2 * r - 1) ∣ u ^ 2 - v ^ 2
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `balWidth_pow_iff` (0.182), `n1_core_square_iff` (0.176)*

## 16. `BTL-block-shift`

**Row.** block shift law: for a word w of length j the section operators send the state (3^j d, 3^{j+i}) to (d + 3^i packWord(w), 3^{j+i}), every such word survives, and at i = 0, j = e the 3^e words of length e reach exactly the states d + t for t in the balanced window W_e = [-(3^e-1)/2, (3^e-1)/2]; the shift is the balanced value packWord(w) an

**Candidate.** `residualAlong_linState_pow` &mdash; kernel-checked, `BTCalculus/PadicLiftingState.lean:302`

> **Target 4.** The block shift law. A singular branch with derivative valuation at least `w.length` is fully ternary along `w`, and the state it reaches is shifted by the *balanced value* of the word, scaled by the excess `3 ^ i`: 𝔇_w (3^j d + 3^(j+i) x) = (d + 3^i · packWord w) + 3^(j+i) x, j = |w|. At `i = 0` this is the leaf law: the `3 ^ e` words of length `e` reach the states `d + packWord w`, and `packWord` is injective on words of a fixed length, so those shifts run over a complete residue system modulo `3 ^ e`. That is what makes the shifted family separate residues; note the shift is the balanced value of the word and not its digit sum.

```lean
theorem residualAlong_linState_pow :
    ∀ (w : List ℤ) (i : ℕ) (d : ℤ),
      residualAlong w (linState (3 ^ w.length * d) (3 ^ (w.length + i)))
        = linState (d + 3 ^ i * packWord w) (3 ^ (w.length + i))
  | [], i, d => by simp [residualAlong, packWord_nil]
  | a :: w, i, d => by
```

**Jev.** picks `residualAlong_linState_pow` as well, at 0.81.

*Runners-up: `outputAlong_linState_pow` (0.109), `linState_root_iff` (0.083)*

*If this row describes a definition rather than a theorem: `linState`, `henselTrit`*

## 17. `BTM-x3-depth`

**Row.** for every balanced-Monna endpoint pair u=zeta+2*3^n, v=zeta-2*3^n one has u^3-v^3=4*3^n(3 zeta^2+4*3^{2n}) and therefore t=v_3(u^3-v^3)=n+min(1+2 v_3(zeta), 2n), or t=3n when zeta=0; the two arguments of the minimum have opposite parity whenever zeta is nonzero

**Candidate.** `monnaEndpoint_val_parity` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:93`

> The two arguments of the depth minimum have opposite parity when `ζ ≠ 0`.

```lean
theorem monnaEndpoint_val_parity (n : ℕ) {ζ : ℚ} (_hζ : ζ ≠ 0) :
    Odd (1 + 2 * padicValRat 3 ζ) ∧ Even (2 * (n : ℤ))
```

**Jev.** picks `monnaEndpoint_cube_val` at 0.92, not the scorer's candidate.

**Jev's candidate.** `monnaEndpoint_cube_val` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:163`

> Combined 3-adic valuation law of `BTM-x3-depth`.

```lean
theorem monnaEndpoint_cube_val (n : ℕ) (ζ : ℚ) :
    padicValRat 3 (monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3)
      = if ζ = 0 then 3 * (n : ℤ)
        else (n : ℤ) + min (1 + 2 * padicValRat 3 ζ) (2 * (n : ℤ))
```

*Runners-up: `monnaEndpoint_cube_val_of_ne` (0.143), `monnaEndpoint_factor_ne` (0.133)*

*If this row describes a definition rather than a theorem: `monnaEndpointU`, `monnaEndpointV`*

## 18. `BTM-x3-no-preserve`

**Row.** cubing never sends a balanced-Monna endpoint pair to an endpoint pair: 3 zeta^2+4*3^{2n} is never +/- 3^k, so u^3-v^3 is never +/- 4*3^k and B(u^3)=B(v^3) never holds

**Candidate.** `monnaEndpoint_cube_diff_ne_four_three_pow` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:277`

> Cubing an endpoint pair never produces difference `4·3^k`.

```lean
theorem monnaEndpoint_cube_diff_ne_four_three_pow (n k : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ 4 * (3 : ℚ) ^ k
```

**Jev.** picks `monnaEndpoint_cube_diff_ne_pm_four_three_pow` at 0.94, not the scorer's candidate.

**Jev's candidate.** `monnaEndpoint_cube_diff_ne_pm_four_three_pow` &mdash; kernel-checked, `BTCalculus/MonnaEndpointCube.lean:311`

> Arithmetic obstruction of `BTM-x3-no-preserve`: `u³−v³` is never `±4·3^k`. Endpoint collisions of the balanced Monna map are pairs whose difference is `±4·3^k` (with the named tails). The difference obstruction is therefore enough for non-preservation; `B` is not defined in this module.

```lean
theorem monnaEndpoint_cube_diff_ne_pm_four_three_pow (n k : ℕ) (ζ : ℚ) :
    monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ 4 * (3 : ℚ) ^ k ∧
      monnaEndpointU n ζ ^ 3 - monnaEndpointV n ζ ^ 3 ≠ -(4 * (3 : ℚ) ^ k)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `monnaEndpoint_cube_diff_ne_neg_four_three_pow` (0.294), `monnaEndpoint_factor_ne` (0.2)*

*If this row describes a definition rather than a theorem: `monnaEndpointU`, `monnaEndpointV`*

## 19. `BTC-constructor-sum-class`

**Row.** for U,V,W in {S,I+,I-,N}, the identity U(x)+V(y)=W(x+y) holds for all integers iff it is one of the eight concrete triples (S,S,S), (N,N,N), (I+,S,I+), (S,I+,I+), (I-,S,I-), (S,I-,I-), (I+,I-,S), (I-,I+,S); same-sign I+ or I- and mixed N+S are not constructor identities

**Candidate.** `exactTriple_characterization` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:108`

> The six parameterized rows, written as the eight concrete triples (`I_a` is a parameter in the informal statement).

```lean
theorem exactTriple_characterization (U V W : AffineCtor) :
    exactTriple U V W ↔
      (U = S ∧ V = S ∧ W = S) ∨
      (U = N ∧ V = N ∧ W = N) ∨
      (U = Ip ∧ V = S ∧ W = Ip) ∨
      (U = S ∧ V = Ip ∧ W = Ip) ∨
      (U = Im ∧ V = S ∧ W = Im) ∨
      (U = S ∧ V = Im ∧ W = Im) ∨
```

**Jev.** picks `apply_add_eq_iff` at 0.79, not the scorer's candidate.

**Jev's candidate.** `apply_add_eq_iff` &mdash; kernel-checked, `BTCalculus/RewriteAddBoundary.lean:89`

```lean
theorem apply_add_eq_iff (U V W : AffineCtor) :
    (∀ x y : ℤ, U.apply x + V.apply y = W.apply (x + y)) ↔
      exactTriple U V W
```

*Runners-up: `apply_add_eq_iff` (0.077), `carry_of_add` (0.0)*

*If this row describes a definition rather than a theorem: `exactTriple`, `DLocal`*

## 20. `BTN-sdrm-lambda3-translate`

**Row.** At λ=3, translation by 3k preserves every output stream: signedTrace 3 (s+3k) w = signedTrace 3 s w. This symmetry is not origin-reachable when max|u|≤1.

**Candidate.** `signedTrace_nil` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualMinimality.lean:17`

```lean
theorem signedTrace_nil (gain s : ℤ) : signedTrace gain s [] = []
```

**Jev.** picks `lambda3_trace_translate` at 0.81, not the scorer's candidate.

**Jev's candidate.** `lambda3_trace_translate` &mdash; kernel-checked, `Problems/BalancedTernary/SignedDigitResidualMinimality.lean:212`

```lean
theorem lambda3_trace_translate (s k : ℤ) :
    ∀ w, signedTrace 3 (s + 3 * k) w = signedTrace 3 s w
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `signedTrace_cons` (0.167), `signedOut_ne_of_not_cong` (0.077)*

*If this row describes a definition rather than a theorem: `signedTrace`, `natVal3`*

## 21. `J-near-tight-scale-bounds`

**Row.** The local Juggler remainder satisfies 0≤ρ<2T+1, hence η=ρ/T^2 < 2/T + 1/T^2 and 1+η < ((T+1)/T)^2. For the mixed itinerary OOE, 1+q = (1+η0)^3 (1+η1)^2 (1+η2)^4, and 1+q is strictly below the successor-ratio product ((T0+1)/T0)^6 ((T1+1)/T1)^4 ((T2+1)/T2)^8. The same bound at a successor start y depends only on the itinerary of y.

**Candidate.** `large_lambda_successor_q_bound` &mdash; kernel-checked, `Problems/Juggler/NearTightScale.lean:201`

> The `OOE` successor bound depends only on the itinerary of `y`. A large-`λ` predecessor enters only by making `y` large.

```lean
theorem large_lambda_successor_q_bound {y : ℕ}
    (hw : follows y ooeWord) :
    slackNum y ooeWord *
        floorPower y ^ 6 *
        floorPower (floorPower y) ^ 4 *
        floorPower (floorPower (floorPower y)) ^ 8 <
      slackDen y ooeWord *
        (floorPower y + 1) ^ 6 *
```

**Jev.** picks `ooe_one_plus_slack_lt_succ_ratio` at 0.37, not the scorer's candidate.

**Jev's candidate.** `ooe_one_plus_slack_lt_succ_ratio` &mdash; kernel-checked, `Problems/Juggler/NearTightScale.lean:112`

> Upper bound `1+q_OOE < ((T0+1)/T0)^6 ((T1+1)/T1)^4 ((T2+1)/T2)^8`.

```lean
theorem ooe_one_plus_slack_lt_succ_ratio {n : ℕ}
    (hw : follows n ooeWord) :
    slackNum n ooeWord *
        floorPower n ^ 6 *
        floorPower (floorPower n) ^ 4 *
        floorPower (floorPower (floorPower n)) ^ 8 <
      slackDen n ooeWord *
        (floorPower n + 1) ^ 6 *
```

*Runners-up: `ooe_one_plus_slack_lt_succ_ratio` (0.15), `even_remainder_bound` (0.118)*

## 22. `J-persistent-implies-expanding`

**Row.** For n≥2, PersistentOddResidual x y if and only if PersistentExpandingResidual x y. A contracting residual cannot overshoot, and 2^k=3^o is impossible for a nonempty residual. The expanding qualifier of a persistent residual is therefore redundant.

**Candidate.** `persistent_odd_residual_expanding` &mdash; kernel-checked, `Problems/Juggler/ExpandingGrammar.lean:113`

> Persistence is already expansion: a contracting residual cannot overshoot `n ≥ 2`.

```lean
theorem persistent_odd_residual_expanding {x y : ℕ}
    (hx : 2 ≤ x) (h : PersistentOddResidual x y) :
    PersistentExpandingResidual x y
```

**Jev.** picks `persistent_expanding_iff_odd` at 1.0, not the scorer's candidate.

**Jev's candidate.** `persistent_expanding_iff_odd` &mdash; kernel-checked, `Problems/Juggler/ExpandingGrammar.lean:138`

> On `n ≥ 2`, the expanding qualifier of a persistent residual is redundant.

```lean
theorem persistent_expanding_iff_odd {x y : ℕ} (hx : 2 ≤ x) :
    PersistentExpandingResidual x y ↔ PersistentOddResidual x y
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `persistent_expanding_iff_odd` (0.462), `expanding_oddEvenBlock_ratio` (0.133)*

*If this row describes a definition rather than a theorem: `expandingItinerary`, `maxExpandingEvens`*

## 23. `J-itinerary-semantics`

**Row.** For every natural n and finite parity itinerary w, follows n w if and only if the actual length-|w| Juggler itinerary of n equals w. The itinerary image equals the |w|-fold iterate, and images and realization compose under word concatenation.

**Candidate.** `image_eq_iterate` &mdash; kernel-checked, `Problems/Juggler/Itinerary.lean:111`

> The image depends on a word only through its length: following `w` from `n` lands where `w.length` steps of `J` land. This is what lets the cycle layer move between word statements and orbit statements.

```lean
theorem image_eq_iterate (n : ℕ) : ∀ w, image n w = floorPower^[w.length] n
```

**Jev.** picks `follows_iff_itinerary` at 0.87, not the scorer's candidate.

**Jev's candidate.** `follows_iff_itinerary` &mdash; kernel-checked, `Problems/Juggler/Itinerary.lean:66`

```lean
theorem follows_iff_itinerary (n : ℕ) : ∀ w : List Branch,
    follows n w ↔ itinerary n w.length = w
  | [] => by simp [follows, itinerary]
  | .even :: w => by
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Runners-up: `itinerary_length` (0.118), `image_word` (0.118)*

*If this row describes a definition rather than a theorem: `follows`, `followsB`*

## 24. `J-inverse-preimage-asymmetry`

**Row.** The even fiber J(n)=m is the parity-restricted square interval m² ≤ n < (m+1)², while the odd fiber is the parity-restricted cube-to-square interval m² ≤ n³ < (m+1)²; any odd fiber contains at most one integer.

**Candidate.** `odd_cube_interval_of_odd_cbrt_implies_square` &mdash; kernel-checked, `Problems/Juggler/Preimages.lean:199`

```lean
theorem odd_cube_interval_of_odd_cbrt_implies_square {n a : ℕ}
    (hodd : n % 2 = 1)
    (hcbrt : Nat.nthRoot 3 (a ^ 8) % 2 = 1)
    (h : a ^ 8 ≤ n ^ 3 ∧ n ^ 3 < (a ^ 4 + 1) ^ 2) :
    n.sqrt ^ 2 = n
```

**Jev.** picks `odd_preimage_unique` at 0.43, not the scorer's candidate.

**Jev's candidate.** `odd_preimage_unique` &mdash; kernel-checked, `Problems/Juggler/Preimages.lean:705`

> An odd one-step preimage `{n : m^2 ≤ n^3 < (m+1)^2}` has at most one point.

```lean
theorem odd_preimage_unique {m a b : ℕ}
    (ha : m ^ 2 ≤ a ^ 3 ∧ a ^ 3 < (m + 1) ^ 2)
    (hb : m ^ 2 ≤ b ^ 3 ∧ b ^ 3 < (m + 1) ^ 2) :
    a = b
```

*Runners-up: `floorPower_odd_eq_iff_cube_interval` (0.19), `noncube_odd_cbrt_fourth_window_cube_even` (0.188)*

*If this row describes a definition rather than a theorem: `itineraryEOO`, `itineraryOOE`*

## 25. `J-finite-progress-boundary`

**Row.** Universal FiniteProgress for starts above one implies universal reachability of one. Every even start n ≥ 2 and every odd start n ≥ 2 whose first image is even has FiniteProgress; consequently, any start without FiniteProgress is odd and has an odd first image. This isolates the automatic odd-to-odd frontier without proving universal prog

**Candidate.** `odd_even_finiteProgress` &mdash; kernel-checked, `Problems/Juggler/Progress.lean:78`

> Odd `n ≥ 2` whose first image is even has finite progress: `OE`.

```lean
theorem odd_even_finiteProgress {n : ℕ} (hn : 2 ≤ n)
    (hodd : n % 2 = 1) (heven : floorPower n % 2 = 0) :
    FiniteProgress n
```

**Jev.** picks `reachesOne_of_all_finiteProgress` at 0.34, not the scorer's candidate.

**Jev's candidate.** `reachesOne_of_all_finiteProgress` &mdash; kernel-checked, `Problems/Juggler/Progress.lean:57`

> If every `n > 1` has finite progress, every positive integer reaches `1`. The hypothesis is not proved here.

```lean
theorem reachesOne_of_all_finiteProgress
    (h : ∀ n, 1 < n → FiniteProgress n) :
    ∀ n, 1 ≤ n → ReachesOne n
```

*Runners-up: `finiteProgress_of_imageLt` (0.208), `finiteProgress_of_not_odd_odd` (0.2)*

*If this row describes a definition rather than a theorem: `FiniteProgress`*

## 26. `J-o7eeee-gap`

**Row.** If n ≥ 2 follows the Juggler word O^7, then T^7(n) ≥ (n+1)^16. In particular the EEEE inverse cell [n^16, (n+1)^16) is empty of seven-odd images, so O^7 EEEE is not a cycle itinerary. Lean theorems o7_image_ge_succ_pow16 and no_cycle_itinerary_oooooooeeee in O7EEEEGap.lean. Proof: no_follows_seven_odds_of_lt256 excludes n < 256; on an O^7

**Candidate.** `image_one_sevenOdds` &mdash; kernel-checked, `Problems/Juggler/O7EEEEGap.lean:27`

```lean
theorem image_one_sevenOdds : image 1 sevenOdds = 1
```

**Jev.** picks `o7_image_ge_succ_pow16` at 0.97, not the scorer's candidate.

**Jev's candidate.** `o7_image_ge_succ_pow16` &mdash; kernel-checked, `Problems/Juggler/O7EEEEGap.lean:331`

```lean
theorem o7_image_ge_succ_pow16 {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n sevenOdds) :
    (n + 1) ^ 16 ≤ image n sevenOdds
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `o7_image_ge_succ_pow16`, `no_cycle_itinerary_oooooooeeee`*

*Runners-up: `o7_image_ge_succ_pow16` (0.081), `no_cycle_itinerary_oooooooeeee` (0.081)*

*If this row describes a definition rather than a theorem: `itineraryO7EEEE`*

## 27. `J-first-even-overshoots`

**Row.** On a MinimalNonTerm or CycleMin start, the first even residual always overshoots: T(O^a E)(n) > n and the even residual sits at or above (n+1)^2. The return-to-n cell of the first-even dichotomy is an even-count-1 cycle itinerary, now excluded by no_cycle_itinerary_even_count_le_three. Lean theorems minimal_first_even_overshoots and cycle

**Candidate.** `minimal_first_even_overshoots` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:584`

> On a `MinimalNonTerm` start the first even residual always overshoots. The return cell is an even-count-1 cycle itinerary. This is not a halt theorem.

```lean
theorem minimal_first_even_overshoots {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
      n < image n (oddEvenBlock a 1)
```

**Jev.** answered an earlier version of this row or of its file; rerun `jev-propose`.

*Statement names: `minimal_first_even_overshoots`, `cycleMin_first_even_overshoots`*

*Runners-up: `cycleMin_first_even_overshoots` (0.3), `cycleMin_max_ge_succ_sq` (0.278)*

## 28. `J-survivor-count-decay`

**Row.** The never-contracting word count N_d of the rate-free density-one reduction (rows J-equidistribution-implies-density-one, J-rate-free-density-one) is identified with a binomial tail and provably decays, closing the link PaperBMarkov's header listed as written mathematics. (i) count_oddCount_ge: length-d parity words with at least a odd le

**Candidate.** `neverCertified_density_zero` &mdash; kernel-checked, `Problems/Juggler/PaperBSurvivorDecay.lean:326`

> **The assembled conditional Theorem 6.1.** Under per-class fairness, the never-certified starts have natural density zero: at each fixed depth the uncertified ratio tends to `N_d / 2^d`, and that bound itself tends to zero as `d → ∞`. The hypothesis `FairClasses` is exactly what remains open.

```lean
theorem neverCertified_density_zero (h : FairClasses) :
    Tendsto
      (fun N : ℕ =>
        (((Icc 1 N).filter fun n => ¬HasFiniteCoeffStop n).card : ℝ) / N)
      atTop (𝓝 0)
```

**Jev.** picks `neverCertified_density_zero` as well, at 0.74.

*Statement names: `count_oddCount_ge`, `oddCount_ge_of_mem_neverNeg`, `neverNegCount_div_pow_le_theta`, `neverNegCount_div_pow_tendsto_zero`, `neverCertified_density_zero`, `neverNegWords_five`, `uncertified_fraction_depth_five`, `neverNegCount_one`, `neverNegCount_two`, `neverNegCount_three`, `neverNegCount_four`, `neverNegCount_five`, `neverNegCount_six`, `neverNegCount_seven`, `neverNegCount_eight`*

*Runners-up: `neverNegCount_five` (0.087), `neverNegCount_div_pow_tendsto_zero` (0.08)*

*If this row describes a definition rather than a theorem: `FairClasses`*

## 29. `J-cyclemax-succ-sq`

**Row.** On a CycleMin start n ≥ 2 the cycle maximum satisfies (n+1)^2 ≤ M. Equivalently, on a CycleMax the rotated minimum m satisfies (m+1)^2 ≤ M, so T(M) > m. The first-cell family m^2 < M < (m+1)^2 is impossible. cycle_distinguished_order_succ_sq is the distinguished-order package with that scale. Corollary of cycleMin_first_even_overshoots: t

**Candidate.** `cycleMin_max_ge_succ_sq` &mdash; kernel-checked, `Problems/Juggler/EvenCountThree.lean:669`

> On a cycle minimum the maximum sits at or above `(n+1)^2`. The first even residual already overshoots, so the first-cell family `n^2 < M < (n+1)^2` is impossible. Not a halt theorem.

```lean
theorem cycleMin_max_ge_succ_sq {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ i < w.length,
      (∀ j < w.length, floorPower^[j] n ≤ floorPower^[i] n) ∧
        floorPower^[i] n % 2 = 0 ∧
          (n + 1) ^ 2 ≤ floorPower^[i] n
```

**Jev.** answered an earlier version of this row or of its file; rerun `jev-propose`.

*Statement names: `cycle_distinguished_order_succ_sq`, `cycleMin_first_even_overshoots`, `cycleMin_max_ge_succ_sq`, `cycleMax_min_succ_sq_le`, `cycleMax_landing_gt_min`, `cycleMax_exists_min_succ_sq`*

*Runners-up: `cycleMax_min_succ_sq_le` (0.222), `minimal_first_even_overshoots` (0.214)*

## 30. `J-cyclemin-transport-oo`

**Row.** On a CycleMin, after the first O^a E with a ≥ 2, an immediate odd run of length at least two overshoots the landing y = T_{O^a E}(n) > n: the next two-odd residual is at least (y+1)^2, hence at least (n+2)^2. Lean: cycleMin_transport_second_oo, cycleMin_transport_second_oo_ge in CycleMinObstruction.lean. The second residual lies outside t

**Candidate.** `cycleMin_transport_second_oo` &mdash; kernel-checked, `Problems/Juggler/CycleMinObstruction.lean:60`

> After the first `O^a E` on a `CycleMin`, an immediate odd run of length at least two overshoots the landing `y`: the next two-odd residual is at least `(y+1)^2`.

```lean
theorem cycleMin_transport_second_oo {n a b : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (_ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : CycleMin n
      (oddEvenBlock a 1 ++ List.replicate b Branch.odd ++ v)) :
    (image n (oddEvenBlock a 1) + 1) ^ 2 ≤
      image (image n (oddEvenBlock a 1)) (List.replicate 2 Branch.odd)
```

**Jev.** picks `cycleMin_transport_second_oo` as well, at 0.37.

*Statement names: `cycleMin_transport_second_oo`, `cycleMin_transport_second_oo_ge`*

*Runners-up: `cycleMin_transport_second_oo_ge` (0.27), `follows_replicate_odd_of_le` (0.029)*

## 31. `J-cyclemin-first-oo-r-bound`

**Row.** Let x1 = T_{O^{a0} E}(n) and B = T_OE. If O^{a0} E follows at n, (OE)^r follows at x1, and B^r(x1) ≥ n, then 2^{2r+a0+1} ≤ 3^{a0+r}. Write R(a0) for the largest such r. Then R(2)=0, R(3)=1, R(4)=3. This is an AboveAnchor / isolated-prefix theorem, not a cycle-return theorem. On a CycleMin-shaped prefix this bounds isolated-OE transport be

**Candidate.** `isolatedOddSurvival_bound` &mdash; kernel-checked, `Problems/Juggler/FirstInternalOO.lean:74`

> Isolated-odd survival bound: staying at least `n` forces `2^{a+2r+1} ≤ 3^{a+r}`. The `O^a E` side is `power_bound_word` (`EnvelopeState.of_follows`); the `(OE)^r` side is `repeated_oe_scale`.

```lean
theorem isolatedOddSurvival_bound {n a r : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix a r))
    (hge : n ≤ image n (isolatedPrefix a r)) :
    isolatedOESurvives a r
```

**Jev.** picks `isolated_oe_ge_implies_exponent` at 0.83, not the scorer's candidate.

**Jev's candidate.** `isolated_oe_ge_implies_exponent` &mdash; kernel-checked, `Problems/Juggler/FirstInternalOO.lean:124`

> Compatibility name of `isolatedOddSurvival_bound`.

```lean
theorem isolated_oe_ge_implies_exponent {n a r : ℕ} (hn : 2 ≤ n)
    (hw : follows n (isolatedPrefix a r))
    (hge : n ≤ image n (isolatedPrefix a r)) :
    2 ^ (a + 2 * r + 1) ≤ 3 ^ (a + r)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `isolatedOddSurvival_bound`, `isolated_oe_ge_implies_exponent`, `isolated_oe_lt_of_scale_gap`, `isolated_oe_r_max_two`*

*Runners-up: `isolated_oe_ge_implies_exponent` (0.118), `isolated_oe_lt_of_scale_gap` (0.077)*

*If this row describes a definition rather than a theorem: `FirstInternalOO`, `isolatedPrefix`*

## 32. `J-ce-third-residual-preimages`

**Row.** If n ≥ 2 follows OOEOOEOO, then T_OOEOOEOO(n) < n^3 because x^{256} ≤ n^{729} forbids n^3 ≤ x (768 > 729). If n follows OOEOOEOOE, then T_OOEOOEOOE(n) < n^2 because y^{512} ≤ n^{729} forbids n^2 ≤ y (1024 > 729). A CE that follows OOEOOE follows OOEOOEOO. On MinimalNonTerm a completed third OOE cannot land even: an even landing below n^2 

**Candidate.** `minimal_ooeooeooe_not_even_landing` &mdash; kernel-checked, `Problems/Juggler/Escape.lean:309`

> On a CE, a completed third `OOE` cannot land even: the landing is below `n^2`, so an even landing is descent. This is not a PE theorem.

```lean
theorem minimal_ooeooeooe_not_even_landing {n : ℕ}
    (h : MinimalNonTerm n) (hw : follows n itineraryOOEOOEOOE) :
    image n itineraryOOEOOEOOE % 2 = 1
```

**Jev.** answered an earlier version of this row or of its file; rerun `jev-propose`.

*Runners-up: `minimal_ooeooeooeoe_not_even_landing` (0.32), `minimal_ooeooeooeoeo_not_even` (0.222)*

*If this row describes a definition rather than a theorem: `itineraryOOEOOEOO`, `itineraryOOEOOEOOE`*

## 33. `J-cube-odd-even-reset`

**Row.** If n ≥ 2 and n^2 ≤ x < n^3 with x odd, then n^3 ≤ T(x) < n^5 and T(x)^2 < n^9. If T(x) is even, the first return satisfies n ≤ T^2(x) < x < n^3 and T^2(x)^4 < n^9. If T(x) is odd, then x < T^2(x) and n^4 ≤ T^2(x). An even reset that is itself even and already below n^2 is FiniteProgress; on MinimalNonTerm that case is impossible. This is 

**Candidate.** `aboveAnchor_not_odd_even` &mdash; kernel-checked, `Problems/Juggler/MinimumRelative.lean:107`

> An `OE` start cannot stay at or above the anchor: the first even residual is below `n^2`.

```lean
theorem aboveAnchor_not_odd_even {n : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (h : AboveAnchor n (.odd :: .even :: v)) : False
```

**Jev.** none of these, at 0.96.  Read the row for a claim broader than any one declaration here, or a declaration narrower than the row.

*Runners-up: `even_ge_sq_of_aboveAnchor` (0.032), `aboveAnchor_isolatedOddSurvival` (0.03)*

*If this row describes a definition rather than a theorem: `AboveAnchor`*

## 34. `J-small-cycle-census-ten`

**Row.** No itinerary of length at most ten is a Juggler cycle itinerary at any n ≥ 2; equivalently a nontrivial Juggler cycle, if one exists, has period at least eleven. Lengths ≤ 8 are the census J-small-cycle-census-eight; lengths 9 and 10 are excluded by the finance inequality at the residual floor 12 (no_cycle_itinerary_length_nine, no_cycle_

**Candidate.** `no_cycle_itinerary_length_le_ten` &mdash; kernel-checked, `Problems/Juggler/CycleFinanceLeftovers.lean:224`

> Census extension: no cycle itinerary of length at most `10`. Lengths `≤ 8` are the Lean census; `9` and `10` are the finance inequality.

```lean
theorem no_cycle_itinerary_length_le_ten {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hlen : w.length ≤ 10) : ¬CycleItinerary n w
```

**Jev.** answered an earlier version of this row or of its file; rerun `jev-propose`.

*Statement names: `no_cycle_itinerary_length_nine`, `no_cycle_itinerary_length_ten`, `no_cycle_itinerary_length_le_ten`*

*Runners-up: `finance_contradicts_min_two_hundred_sixty_one` (0.206), `no_cycle_itinerary_length_le_nineteen` (0.172)*

*If this row describes a definition rather than a theorem: `financeRows53`, `financeRows257`*

## 35. `J-cyclemin-defect-finance-kill`

**Row.** The defect-sum finance inequality (the certified identity of Paper A Theorem 4.6, previously human) and the walk-charge kill criterion (Theorem 5.9 mechanism), Lean end to end (DefectFinance.lean). Finance: on a CycleMin cycle with minimum n ≥ 400, 1 − 2^L/3^o ≤ (6/5)·Σ_k 1/(x_k·log x_k) (cycleMin_defect_finance). Ingredients all Lean: pe

**Candidate.** `cycleMin_hug_kill_criterion` &mdash; kernel-checked, `Problems/Juggler/DefectFinance.lean:439`

> **The walk-charge kill criterion** (Paper A Theorem 5.9 mechanism, Lean form): every minimum-based cycle at `n ≥ 400` with positive reduced log-base `ν = log n − D` must satisfy `1 − 2^L/3^o ≤ (6/5) · Σ_k g(hugWeight k)` with the charge evaluated at the reduced base. The kill tables verify the numeric failure of this inequality per surviving length; that evaluation stays verified computation, the implication is Lean.

```lean
theorem cycleMin_hug_kill_criterion {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w)
    (hν : 0 < Real.log n - transportDeficit n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * ∑ k ∈ Finset.range w.length,
        stateCharge (Real.log n - transportDeficit n w) (hugWeight k)
```

**Jev.** picks `cycleMin_defect_finance` at 0.46, not the scorer's candidate.

**Jev's candidate.** `cycleMin_defect_finance` &mdash; kernel-checked, `Problems/Juggler/DefectFinance.lean:369`

> **Defect-sum finance inequality** (the certified identity of Paper A Theorem 4.6, Lean form): on a minimum-based cycle with minimum `n ≥ 400`, `1 − 2^L/3^o ≤ (6/5) · Σ_k 1/(x_k·log x_k)`.

```lean
theorem cycleMin_defect_finance {n : ℕ} {w : List Branch}
    (hn : 400 ≤ n) (h : CycleMin n w) :
    1 - (2 : ℝ) ^ w.length / 3 ^ oddCount w ≤
      1.2 * ∑ k ∈ Finset.range w.length,
        1 / ((floorPower^[k] n : ℝ) * Real.log (floorPower^[k] n))
```

*Statement names: `cycleMin_defect_finance`, `neg_log_one_sub_le_sixth`, `log_floorPower_even_ge_sub`, `log_floorPower_odd_ge_sub`, `log_floorPower_even_le`, `log_floorPower_odd_le`, `cycleMin_log_le_weight`, `cycleMin_charge_prefix`, `cycleMin_hug_kill_criterion`*

*Runners-up: `cycleMin_defect_finance` (0.134), `log_floorPower_even_ge_sub` (0.11)*

*If this row describes a definition rather than a theorem: `prefixCharge`*

## 36. `J-loglog-clock-even-chain-burst-lean`

**Row.** even_chain_mem_burst: if the first k states of the orbit of n are even and floorPower^[k] n = m, then m^(2^k) <= n < (m + 1)^(2^k); proved by induction from the one-step cell Nat.sqrt n ^ 2 <= n < (Nat.sqrt n + 1) ^ 2 (sqrt_cell) and floorPower_even_eq. Corollary even_chain_log_offset (1 <= m): 2^k log m <= log n < 2^k log (m + 1), i.e. i

**Candidate.** `even_chain_mem_burst` &mdash; kernel-checked, `Problems/Juggler/LogLogClock.lean:171`

> **The even chain lands in the burst interval.** If the first `k` states of the orbit of `n` are even and the `k`-th iterate is `m`, then `m^(2^k) ≤ n < (m+1)^(2^k)`.

```lean
theorem even_chain_mem_burst :
    ∀ (k n m : ℕ), (∀ i, i < k → (floorPower^[i] n) % 2 = 0) → floorPower^[k] n = m →
      m ^ (2 ^ k) ≤ n ∧ n < (m + 1) ^ (2 ^ k)
```

**Jev.** picks `even_chain_mem_burst` as well, at 0.96.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `even_chain_mem_burst`, `sqrt_cell`, `even_chain_log_offset`*

*Runners-up: `even_chain_log_offset` (0.226), `not_reachesOne_even_chain_ge` (0.139)*

*If this row describes a definition rather than a theorem: `alphaClock`, `WalkStep`*

## 37. `J-loglog-clock-band-word-forced-lean`

**Row.** Inside the hug band the parity letter is forced. band_step_forced_odd: from u < 1 a step staying in [0, 1 + alphaClock) must be the odd one, v = u + alphaClock (the even step goes negative). band_step_forced_even: from 1 <= u it must be the even one, v = u - 1 (the odd step exceeds the band). band_successor_unique: a band-confined walk ha

**Candidate.** `band_successor_unique` &mdash; kernel-checked, `Problems/Juggler/LogLogClock.lean:143`

> **The band walk is the rotation by `alphaClock`.** A walk confined to the hug band has a single admissible successor at every point, given by the lift of the rotation: `u + alphaClock` below `1`, `u - 1` above. So the parity word of a band-confined orbit is determined by nothing but the starting walk — it is the mechanical word of the rotation, the hug itinerary.

```lean
theorem band_successor_unique {u v w : ℝ} (_h0 : 0 ≤ u) (_h1 : u < 1 + alphaClock)
    (hv : WalkStep u v) (hvin : 0 ≤ v ∧ v < 1 + alphaClock)
    (hw : WalkStep u w) (hwin : 0 ≤ w ∧ w < 1 + alphaClock) : v = w
```

**Jev.** picks `band_successor_unique` as well, at 0.95.

*Statement names: `band_step_forced_odd`, `band_step_forced_even`, `band_successor_unique`*

*Runners-up: `band_step_forced_odd` (0.263), `band_step_forced_even` (0.263)*

*If this row describes a definition rather than a theorem: `WalkStep`, `alphaClock`*

## 38. `J-floor-stratifies-even-cylinders-lean`

**Row.** not_reachesOne_even_chain_ge: if n >= 1 does not reach 1 and its first k states are even, then 261^(2^k) <= n. Proof: the k-th iterate is again a failure (backwardClosed_iterate with reachesOne_backwardClosed), hence >= 261 by the Lean floor (reachesOne_of_lt_two_hundred_sixty_one via not_reachesOne_ge; positivity by floorPower_iterate_po

**Candidate.** `not_reachesOne_even_chain_ge` &mdash; kernel-checked, `Problems/Juggler/LogLogClock.lean:241`

> **The floor stratifies the failure set.** If `n ≥ 1` does not reach `1` and its first `k` states are even, then `261^(2^k) ≤ n`.

```lean
theorem not_reachesOne_even_chain_ge {n k : ℕ} (hn : 1 ≤ n) (h : ¬ ReachesOne n)
    (hpar : ∀ i, i < k → (floorPower^[i] n) % 2 = 0) : 261 ^ (2 ^ k) ≤ n
```

**Jev.** picks `not_reachesOne_even_chain_ge` as well, at 1.0.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `not_reachesOne_even_chain_ge`, `not_reachesOne_ge`, `even_chain_mem_burst`*

*Runners-up: `even_chain_mem_burst` (0.159), `not_reachesOne_ge` (0.071)*

*If this row describes a definition rather than a theorem: `WalkStep`, `walk`*

## 39. `J-live-count-weight`

**Row.** The live count liveCount N0 N w = #{n in [1,N] : itinerary n |w| = w and n, J n, ..., J^|w| n all exceed N0} is a WeightSplit weight (liveWeight_weightSplit: the two one-letter extensions have disjoint live classes inside the parent's), and juggler_count_le_of_noMomentum instantiates the chain on it: if NoMomentum (liveWeight N0 N) x q de

**Candidate.** `juggler_count_le_of_noMomentum` &mdash; kernel-checked, `formal/Problems/Juggler/LiveCountWeight.lean:146`

> **The Tao-type count on Juggler orbits from no momentum.** If the live count of starts in `{1, …, N}` above the floor `N0` has no momentum at tilt `x` against `q` to depth `d` (`NoMomentum`), then the number of starts that stay above `N0` for `d` steps with at least `k` odd letters is at most `N · a_q^d · exp(c_q δ d) / x^k`.

```lean
theorem juggler_count_le_of_noMomentum (N0 N : ℕ) (x q δ : ℝ) (hx : 1 ≤ x)
    (hq : 0 ≤ q) (d k : ℕ) (hM : NoMomentum (liveWeight N0 N) x q δ d) :
    (((Icc 1 N).filter
        (fun n => liveTo N0 n d ∧ k ≤ oddCount (itinerary n d))).card : ℝ) ≤
      N * (1 + (x - 1) * q) ^ d *
        Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k
```

**Jev.** picks `juggler_count_le_of_noMomentum` as well, at 0.73.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `liveWeight_weightSplit`, `juggler_count_le_of_noMomentum`, `liveCount_sum_oddCount`*

*Runners-up: `liveCount_sum_oddCount` (0.152), `juggler_count_le_of_meanShare` (0.123)*

*If this row describes a definition rather than a theorem: `liveCount`, `liveWeight`*

## 40. `J-mean-share-exceptional-depths`

**Row.** What the mean-share hypothesis does not need, machine-checked. Paper C section 9.3(a) and 9.3(b) were prose; these are the statements. (a) MeanShareOff mu x q d E := sum over t in [0,d) minus E of s_t <= q |[0,d) minus E|, with nothing whatever assumed on the exceptional set E. Then weightGen_le_of_meanShareOff gives Z_d <= Z_0 x^|[0,d) c

**Candidate.** `initial_depths_are_free` &mdash; kernel-checked, `formal/Problems/Juggler/TiltedShare.lean:494`

> **Every bounded prefix of depths is free.** Taking the exceptional set to be the first `k` depths, no assumption whatever on those depths costs more than the constant factor `x^k`. This is Paper C section 9.3(a): the depth-five split, and every split to any fixed depth, cannot bear on the reduction.

```lean
theorem initial_depths_are_free (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d k : ℕ) (hk : k ≤ d) (hM : MeanShareOff μ x q d (Finset.range k)) :
    weightGen μ x d ≤ weightGen μ x 0 * (x ^ k * (1 + (x - 1) * q) ^ (d - k))
```

**Jev.** picks `weightGen_le_of_meanShareOff` at 0.64, not the scorer's candidate.

**Jev's candidate.** `weightGen_le_of_meanShareOff` &mdash; kernel-checked, `formal/Problems/Juggler/TiltedShare.lean:410`

> **Exceptional depths cost a factor `x` each, and nothing more.** Under `MeanShareOff` the depth-`d` tilted mass is at most `Z_0 · x^{|E ∩ [0,d)|} · a_q^{|[0,d) \ E|}`.

```lean
theorem weightGen_le_of_meanShareOff (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d : ℕ) (E : Finset ℕ) (hM : MeanShareOff μ x q d E) :
    weightGen μ x d ≤
      weightGen μ x 0 * (x ^ (Finset.range d ∩ E).card *
        (1 + (x - 1) * q) ^ (Finset.range d \ E).card)
```

*Statement names: `weightGen_le_of_meanShareOff`, `tiltedShare_le_one`, `count_le_of_meanShareOff`, `meanShareOff_empty`, `initial_depths_are_free`, `tower_ratio_lt_one`, `tower_tolerance_half`*

*Runners-up: `weightGen_le_of_meanShareOff` (0.141), `count_le_of_meanShareOff` (0.1)*

*If this row describes a definition rather than a theorem: `MeanShareOff`, `NoMomentum`*

## 41. `J-localized-kernel-arithmetic`

**Row.** Rational bookkeeping only, not an exponential-sum estimate. LocalizedKernel.lean proves absTail_eq: three nested half-averages give (7y+a)/8; threshold_iff and threshold_value: retaining saving 1/96 requires y>=29/48. Legacy companionY=23/32 is explicitly a reference scale, not a production scale; absTail_companion=533/768, target_compani

**Candidate.** `production_formal_effective_saving` &mdash; kernel-checked, `formal/Problems/Juggler/LocalizedKernel.lean:98`

> Pure bookkeeping: the formal tail remains below the trivial interval length by `11/1536`. This arithmetic statement does not assert the shorter-interval estimate or its production application.

```lean
theorem production_formal_effective_saving :
    productionY - absTail productionY A₁ = 11 / 1536
```

**Jev.** none of these, at 0.83.  Read the row for a claim broader than any one declaration here, or a declaration narrower than the row.

*Statement names: `absTail_eq`, `threshold_iff`, `threshold_value`, `absTail_companion`, `target_companion`, `margin_companion`, `productionY_eq_one_sub`, `absTail_production`, `target_production`, `production_lt_threshold`, `production_misses_same_saving`, `production_same_saving_deficit`, `production_formal_effective_saving`, `proportional_chain`, `claimC_balance`, `claimC_output`, `claimC_others_dominated`, `twist_negligible`, `twist_uniform_exponent`*

*Runners-up: `absTail_lt_target` (0.08), `production_misses_same_saving` (0.08)*

*If this row describes a definition rather than a theorem: `absTail`, `absStep`*

## 42. `J-cube-fiber-exact`

**Row.** The OE fiber of a perfect cube is full or exactly alternating. For every a >= 1 and every n with (2a)^4 <= n and n^3 < ((2a)^3+1)^4, floor(n^(3/2)) = Nat.sqrt (n^3) is even (even_cube_fiber_full); for every odd n with (2a+1)^4 <= n and n^3 < ((2a+1)^3+1)^4, Nat.sqrt (n^3) + (n - (2a+1)^4)/2 is odd (odd_cube_fiber_alternating), so consecut

**Candidate.** `odd_cube_fiber_alternating` &mdash; kernel-checked, `formal/Problems/Juggler/CubeFiber.lean:100`

> The fiber-level statement for odd cubes: an odd `n` with `(2a+1)^4 ≤ n` and `n^3 < ((2a+1)^3 + 1)^4` sits at an even offset `2s`, and its image has the parity of `1 + s`. Consecutive fiber elements therefore have opposite image parity.

```lean
theorem odd_cube_fiber_alternating (a n : ℕ) (hodd : n % 2 = 1) (hlo : (2 * a + 1) ^ 4 ≤ n)
    (hhi : n ^ 3 < ((2 * a + 1) ^ 3 + 1) ^ 4) :
    (Nat.sqrt (n ^ 3) + (n - (2 * a + 1) ^ 4) / 2) % 2 = 1
```

**Jev.** none of these, at 0.75.  Read the row for a claim broader than any one declaration here, or a declaration narrower than the row.

*Statement names: `even_cube_fiber_full`, `odd_cube_fiber_alternating`, `cube_fiber_sqrt_even`, `cube_fiber_sqrt_odd`, `cube_fiber_range`*

*Runners-up: `even_cube_fiber_full` (0.076), `cube_fiber_sqrt_odd` (0.067)*

## 43. `J-paper-b-formal-layer-has-an-estimate`

**Row.** Paper B's formal layer now contains an estimate, where before it contained none. THE STANDING POSITION, stated in the paper's own barrel JugglerParityPaper.lean: 'Building it does not corroborate the paper's analysis. Every declaration reachable from here is an identity, a constant, or a threshold; not one of them is an estimate.' That wa

**Candidate.** `theta_eq_exp_neg_klDiv` &mdash; kernel-checked, `formal/Problems/Juggler/PaperBChernoff.lean:96`

> The printed form is `exp(-D(q ‖ 1/2))`.

```lean
theorem theta_eq_exp_neg_klDiv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta q = Real.exp (-klDiv q (1 / 2))
```

**Jev.** picks `theta_lt_one` at 0.98, not the scorer's candidate.

**Jev's candidate.** `theta_lt_one` &mdash; kernel-checked, `formal/Problems/Juggler/PaperBChernoff.lean:110`

> The estimate: the Chernoff factor is strictly below one away from the fair point.

```lean
theorem theta_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hq : q ≠ 1 / 2) : theta q < 1
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `one_sub_inv_lt_log`, `klDiv_pos`, `theta_eq_exp_neg_klDiv`, `theta_lt_one`, `theta_pos`, `theta_pow_lt`*

*Runners-up: `theta_pow_lt` (0.047), `one_sub_inv_lt_log` (0.039)*

*If this row describes a definition rather than a theorem: `klDiv`, `theta`*

## 44. `J-paper-b-transposition-costs-the-barrier-mass`

**Row.** Transposing two adjacent barrier letters costs exactly the mass on the barrier. Grade the surviving parity words of a given length by their surplus h above the barrier. A barrier letter that does not rise acts by stepFlat v h = v h + v (h-1) and kills nothing; one that rises acts by stepRise v h = v (h+1) + v h and loses exactly v 0, the 

**Candidate.** `run_stepRise_stepFlat` &mdash; kernel-checked, `formal/Problems/Juggler/PaperBJumpTransposition.lean:137`

> **What a discontinuity costs.** Transposing one adjacent rise-then-flat pair of barrier letters changes the whole later history by exactly the history of a single point mass on the barrier at the moment of the swap.

```lean
theorem run_stepRise_stepFlat (w : List Bool) (v : Profile) :
    run w (stepRise (stepFlat v))
      = run w (stepFlat (stepRise v)) + run w (barrierMass v)
```

**Jev.** picks `run_stepRise_stepFlat` as well, at 0.71.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `stepRise_stepFlat_eq_add_barrierMass`, `run_add`, `run_stepRise_stepFlat`, `stepRise_barrierMass`, `total_stepFlat_eq_two_mul`, `total_stepRise_add_barrierMass`, `run_stepFlat_stepRise_le`*

*Runners-up: `stepRise_stepFlat_eq_add_barrierMass` (0.167), `total_stepFlat_eq_two_mul` (0.154)*

*If this row describes a definition rather than a theorem: `barrierMass`, `stepFlat`*

## 45. `J-collatz-bridge-is-exact-at-the-word-level`

**Row.** The Juggler-Collatz bridge, stated as theorems over the one shared object, the List Branch word, with no real number and nothing measured in any statement. COLLATZ IS WORD-AFFINE WITH THE CORRECTION POINTING UP: for the shortcut map C (x/2 on evens, (3x+1)/2 on odds) and w = parityWord x d the first d parities of the orbit of x, 2^d * C^d

**Candidate.** `neg_cycle_expanding` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:623`

> **Negative cycles expand.** A cycle of the `ℤ` map at `x ≤ -2` of positive length has `2 ^ d < 3 ^ o` -- Juggler's sign -- because the right-hand side of the cycle equation is positive (the word has an even letter, else the cycle would sit at `-1`) and `x + 1 < 0`.

```lean
theorem neg_cycle_expanding {x : ℤ} {d : ℕ} (hd : 0 < d) (hx : x ≤ -2) (hcyc : shortcutZIter d x = x) :
    2 ^ d < 3 ^ oddCount (parityWordZ x d)
```

**Jev.** picks `word_affine` at 0.79, not the scorer's candidate.

**Jev's candidate.** `word_affine` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:159`

> **Collatz is word-affine.** `2 ^ d · C^d(x) = 3 ^ o · x + wordConst w` with `w` the parity word of `x` and `o` its odd count. The multiplier `3 ^ o / 2 ^ d` is the one Juggler carries on the exponent; the correction is nonnegative.

```lean
theorem word_affine (x d : ℕ) :
    2 ^ d * shortcutCIter d x =
      3 ^ oddCount (parityWord x d) * x + wordConst (parityWord x d)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `word_affine`, `juggler_word_power`, `cycle_contracting`, `juggler_cycle_expanding`, `parityWord_eq_iff`, `image_parityWord`, `allWords_card`*

*Runners-up: `word_affine` (0.071), `image_parityWord` (0.071)*

*If this row describes a definition rather than a theorem: `parityWord`, `shortcutC`*

## 46. `J-survivor-count-is-a-collatz-residue-count`

**Row.** Paper B's survivor count is a Collatz residue count, in Lean. undecidedResidues_card: the number of residues r modulo 2^d whose parity word parityWord r d has no contracting prefix equals neverNegCount d, the N_d of RateFreeDensity; decidedAtResidues_card: the number whose word is a minimal certificate (first contracts at exactly d) equal

**Candidate.** `undecidedResidues_card` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:324`

> **The survivor count is a Collatz count.** Paper B's `N_d` is the number of residue classes modulo `2 ^ d` with no contracting prefix -- the definition of OEIS A076227.

```lean
theorem undecidedResidues_card (d : ℕ) : (undecidedResidues d).card = neverNegCount d
```

**Jev.** picks `undecidedResidues_card` as well, at 0.97.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `undecidedResidues_card`, `image_parityWord`, `le_iter_of_prefixNoncontracting`, `iter_lt_of_exponentGap_class`*

*Runners-up: `neg_cycle_word_is_juggler_shape` (0.066), `exists_residue_of_word` (0.063)*

*If this row describes a definition rather than a theorem: `undecidedResidues`, `parityWord`*

## 47. `J-collatz-even-step-charge-identity`

**Row.** The Collatz walk charge, in natural numbers. Define evenCharge on words by evenCharge [] = 0, evenCharge (even :: w) = 3^(oddCount w) + 2 evenCharge w, evenCharge (odd :: w) = 2 evenCharge w -- in closed form the sum over even positions i of 3^(o - a_i) 2^i with a_i the odd letters before i. Then (wordConst_add_two_pow) wordConst w + 2^|w

**Candidate.** `cycle_even_charge` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:510`

> **The Collatz walk charge, exactly.** On a cycle the surplus `(x + 1)(2 ^ d - 3 ^ o)` is the even-step charge of the word. This is the counterpart of Paper A's finance inequality `n log n (3 ^ o - 2 ^ L) ≤ L 3 ^ o`, as an identity rather than a bound.

```lean
theorem cycle_even_charge {x d : ℕ} (hcyc : shortcutCIter d x = x) :
    (x + 1) * 2 ^ d = (x + 1) * 3 ^ oddCount (parityWord x d) + evenCharge (parityWord x d)
```

**Jev.** picks `two_pow_mul_iter_add_one` at 0.74, not the scorer's candidate.

**Jev's candidate.** `two_pow_mul_iter_add_one` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:492`

> **The affine formula in the `x + 1` coordinate.** Every correction comes from an even step.

```lean
theorem two_pow_mul_iter_add_one (x d : ℕ) :
    2 ^ d * (shortcutCIter d x + 1) =
      3 ^ oddCount (parityWord x d) * (x + 1) + evenCharge (parityWord x d)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `wordConst_add_two_pow`, `two_pow_mul_iter_add_one`, `three_pow_mul_add_one_le`, `cycle_even_charge`, `trivial_cycle_charge`*

*Runners-up: `three_pow_mul_add_one_le` (0.161), `wordConst_add_two_pow` (0.138)*

*If this row describes a definition rather than a theorem: `evenCharge`, `wordConst`*

## 48. `J-juggler-cycle-words-are-collatz-negative-cycle-words`

**Row.** The sign flip on cycles is the sign of x, and Juggler's cycle words are the words of Collatz's negative cycles. On the negative integers the odd step is |x| -> (3|x| - 1)/2, so the correction pushes |x| below the pure multiplier -- Juggler's sign -- and the cycle equation (x + 1)(2^d - 3^o) = evenCharge w >= 0 with x + 1 < 0 forces 2^d < 

**Candidate.** `neg_cycle_word_is_juggler_shape` &mdash; kernel-checked, `Problems/Juggler/CollatzBridge.lean:762`

> **The word-level twin, exactly.** A negative cycle of the `ℤ` map of positive length, read at its least `|x|`, has a word that is prefix-noncontracting and expanding -- the Juggler cycle-word shape of Paper A, with no `delta` exception on this side.

```lean
theorem neg_cycle_word_is_juggler_shape {x : ℤ} {K : ℕ} (hK : 0 < K) (hx : x ≤ -2)
    (hcyc : shortcutZIter K x = x) (hmin : ∀ j, j ≤ K → shortcutZIter j x ≤ x) :
    prefixNoncontracting (parityWordZ x K) ∧ 2 ^ K < 3 ^ oddCount (parityWordZ x K)
```

**Jev.** picks `neg_cycle_word_is_juggler_shape` as well, at 0.84.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `neg_cycle_expanding`, `cycle_contracting`, `neg_prefix_noncontracting`, `neg_cycle_word_is_juggler_shape`, `neg_seventeen_word_is_juggler_shape`, `neg_seventeen_is_least`, `neg_one_cycle`, `neg_five_cycle`, `neg_seventeen_cycle`*

*Runners-up: `neg_prefix_noncontracting` (0.115), `neg_cycle_expanding` (0.093)*

*If this row describes a definition rather than a theorem: `undecidedResidues`, `evenCharge`*

## 49. `J-paper-c-production-words-are-prefix-free`

**Row.** Paper C's finite production words are prefix-free, in Lean, for the whole family rather than for the six the manuscript fixes. Paper C (docs/theory/juggler_fate_almost_all_note.md) builds Theorem 1 from six productions V_k = (OE)^(k-1) OEE with rho_k = (1/2)(3/4)^k, 1 <= k <= 6, and uses their prefix-freeness three times: 'Production word

**Candidate.** `Vword_prefix_iff` &mdash; kernel-checked, `Problems/Juggler/FateProductionWords.lean:66`

> **The production words are prefix-free.** `V_i` is a prefix of `V_j` only when `i = j`; in particular the six words Paper C fixes, `Vword 0` through `Vword 5`, are pairwise prefix-free. The reason is that `V_i` closes with a second `E` exactly where `V_j`, for `j > i`, opens another `OE`.

```lean
theorem Vword_prefix_iff {i j : ℕ} (h : Vword i <+: Vword j) : i = j
```

**Jev.** picks `Vword_prefix_iff` as well, at 0.99.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `Vword_length`, `Vword_oddCount`, `Vword_eq_odd_cons`, `Vword_prefix_iff`, `Vword_six_prefixFree`, `Vword_five`*

*Runners-up: `Vword_five` (0.052), `Vword_six_prefixFree` (0.052)*

*If this row describes a definition rather than a theorem: `Vword`*

## 50. `J-oe-fiber-block-lock`

**Row.** An OE fiber can be unbalanced only by locking onto a rational step of small denominator, and the quantitative form is elementary. For m >= 10^6 and every convergent denominator q of alpha_m = {(3/2) m^(2/3)}, |G_m/H_m - 1/2| <= 4||q alpha_m|| + 5/(2q) + 3.77 q/H_m. PROOF: cut the fiber into blocks of q consecutive members; by Lemma 4.2's 

**Candidate.** `block_count` &mdash; kernel-checked, `formal/Problems/Juggler/FateBlockLock.lean:512`

> **Lemma 1, one block.** On `q` consecutive indices the good count is within `4 (ρ + qη) q + 5/2` of `q/2`. This is the heart of the note's Lemma 1: the block's points are a translate of the `1/q`-grid displaced by at most `ε = ρ + qη`, the grid is split evenly by the arc `[0, 1/2)` up to `1/2` (`gridPoint_half_count`), and at most `4εq + 2` of the indicators move (`gridPoint_near_count`, `fract_lt_half_congr`).

```lean
theorem block_count (x : ℕ → ℝ) (H q j₀ : ℕ) (a η ρ : ℝ) (p : ℤ)
    (hq : 1 ≤ q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hcop : Nat.Coprime p.natAbs q)
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η)
    (hpa : |(q : ℝ) * a - (p : ℝ)| ≤ ρ) (hj₀ : j₀ + q ≤ H) :
    |(#{i ∈ Finset.range q | Int.fract (x (j₀ + i)) < 1 / 2} : ℝ) - (q : ℝ) / 2|
      ≤ 4 * (ρ + (q : ℝ) * η) * (q : ℝ) + 5 / 2
```

**Jev.** picks `block_lock` at 0.96, not the scorer's candidate.

**Jev's candidate.** `block_lock` &mdash; kernel-checked, `formal/Problems/Juggler/FateBlockLock.lean:655`

> **Lemma 1 (block lock).** `docs/theory/juggler_oe_poor_fiber_tail_note.md`, (1.1), in the cleared form. If the first `H` steps of `x` lie in `[a, a + η]` and `a` is within `ρ/q` of the rational `p/q` with `gcd(p, q) = 1`, then the number of `j < H` with `{x j} < 1/2` differs from `H/2` by at most `4 (ρ + qη) H + 5H/(2q) + q`. Dividing by `H` and substituting `ρ = ‖qa‖` gives the note's `|σ - 1/2| ≤ 4‖qa‖ + 5/(2q) + q(1 + 4ηH)/H`; that division is left to the caller so that this statement carries no nonzero-denominator side condition and stays true at `H = 0`.

```lean
theorem block_lock (x : ℕ → ℝ) (H q : ℕ) (a η ρ : ℝ) (p : ℤ)
    (hq : 1 ≤ q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hcop : Nat.Coprime p.natAbs q)
    (hstep : ∀ j, j + 1 < H → a ≤ x (j + 1) - x j ∧ x (j + 1) - x j ≤ a + η)
    (hpa : |(q : ℝ) * a - (p : ℝ)| ≤ ρ) :
    |(#{j ∈ Finset.range H | Int.fract (x j) < 1 / 2} : ℝ) - (H : ℝ) / 2|
      ≤ 4 * (ρ + (q : ℝ) * η) * (H : ℝ) + 5 * (H : ℝ) / (2 * (q : ℝ)) + (q : ℝ)
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `block_lock`, `grid_half_count`, `grid_near_count`, `gridRes_mul_inj`, `grid_reindex`*

*Runners-up: `gridPoint_near_count` (0.124), `gridPoint_half_count` (0.114)*

*If this row describes a definition rather than a theorem: `Unstable`, `gridRes`*

## 51. `J-oe-poor-fiber-tail`

**Row.** The OE fibers whose parity share is bounded away from 1/2 have finite total logarithmic mass, so no set can concentrate on them. For eta_0 in (0,1/2], with P_eta0 = {m : |G_m/H_m - 1/2| >= eta_0} and u_0(eta_0) = max(10^6, (1950/eta_0^2)^3): #(P_eta0 cap (u,2u]) <= 430 u^(2/3)/eta_0^2 for u >= u_0, and sum over m in P_eta0, m > U of 1/m <

**Candidate.** `poor_count_le'` &mdash; kernel-checked, `formal/Problems/Juggler/FatePoorTail.lean:168`

> **Theorem 4, the block count with an explicit constant.** `430 u^{2/3}/η₀²`. The note claims `420`. That figure assumed the second term of Lemma 3 was `Q(Q+1)/2`, the Gauss sum; `resonance_count_le'` delivers `Q(Q+1)`, because `arc_count_le` counts a half-open arc while `‖q A_m‖ ≤ δ` is closed, so each of the `Q` arcs is widened by one point. Carried through, `2·3.77·61.5 + 18 = 481.71` against `0.8825 u^{2/3}` gives `425.11`, so `420` is false and `430` is the honest constant. Nothing downstream moves: the note already records that only the positivity of the exponent matters, never the size of the constant.

```lean
theorem poor_count_le' {u : ℕ} (hu : 10 ^ 6 ≤ u) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)
    (hδ2 : 32 / (η₀ * (2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} : ℝ) ≤ 430 * (u : ℝ) ^ ((2 : ℝ) / 3) / η₀ ^ 2
```

**Jev.** picks `poor_logMass_le` at 0.6, not the scorer's candidate.

**Jev's candidate.** `poor_logMass_le` &mdash; kernel-checked, `formal/Problems/Juggler/FatePoorTail.lean:312`

> **(4.2) of the note.** For `U ≥ 10^6` satisfying the block hypotheses, and every `N`, the `η₀`-poor `m ∈ (U, N]` carry `1/m`-weighted mass at most `2100 U^{-1/3}/η₀²`. This is the summability that makes the poor set logarithmically finite, which is the whole content of the branch: there is nothing for an adversary to concentrate on. The argument is `bad_logMass_le`'s with a different summand.

```lean
theorem poor_logMass_le {U N : ℕ} (hU : 10 ^ 6 ≤ U) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * (U : ℝ) ^ ((1 : ℝ) / 3) - 1)
    (hδ2 : 32 / (η₀ * (2 / 3 * (U : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2) :
    (∑ m ∈ {m ∈ Finset.Ioc U N | Poor η₀ m}, (1 : ℝ) / m) ≤ 2100 * eps U / η₀ ^ 2
```

*Statement names: `poor_count_le'`, `poor_logMass_le`*

*Runners-up: `nonpoor_fiber_logMass_ge` (0.073), `poor_logMass_le` (0.07)*

*If this row describes a definition rather than a theorem: `Poor`*

## 52. `J-oe-averaged-two-productions-reach-the-depth-two-ceiling`

**Row.** With the poor-fiber tail, Paper C's contagion recursion needs only two productions, and they reach the depth-two ceiling. Taking the OE family over all of A cap (x^(3/8), x^(3/4)] rather than over the rest -- legitimate because the E-images are even and the OE-images odd, which is the only disjointness ever used -- Corollary of J-oe-poor-

**Candidate.** `zeta2avg_pos` &mdash; kernel-checked, `formal/Problems/Juggler/FatePoorProduction.lean:526`

> `ζ(100/203) > 0` at `η₀ = 10^{-5}`, by two rational bounds at the 203rd power: `0.710737 ≤ 2^{-100/203}` since `0.710737^{203} ≤ 2^{-100}`, and `0.867868 ≤ (3/4)^{100/203}` since `0.867868^{203} ≤ (3/4)^{100}`; then `0.710737 + (49999/150000)(0.867868) = 1.0000205 > 1`. `100/203 = 0.4926108…`, against the true root `λ_ideal = 0.4926579801…` of `2^{-λ} + (1/3)(3/4)^λ = 1`, and above Paper C's published `λ** = 0.4925715447…`, which is what this certificate exists to clear. It is chosen for margin, not minimality: `67/136` also lies in `(λ**, λ_ideal)` and has the smaller denominator, but leaves only `6.3·10^{-6}` of `ζ` at `η₀ = 0` against this one's `2.71·10^{-5}`, so it would force both a tenfold smaller `η₀` and sharper rational bounds for no gain in the theorem. (`33/67`, the previous convergent, falls just short of `λ**` outright.) The margin here, `2.05·10^{-5}`, is what `η₀ = 10^{-5}` leaves of that `2.71·10^{-5}`; break-even is `η₀ = 4.69·10^{-5}`. `oe_rest_average.exponent_certificate` re-derives all of it in exact arithmetic.

```lean
theorem zeta2avg_pos :
    0 < ∑ i, coef2avg (1 / 100000) i * rate2 i ^ ((100 : ℝ) / 203) - 1
```

**Jev.** picks `logMass_contagion_averaged` at 0.77, not the scorer's candidate.

**Jev's candidate.** `logMass_contagion_averaged` &mdash; kernel-checked, `formal/Problems/Juggler/FatePoorProduction.lean:548`

> **Contagion above Paper C's published exponent, as a log-mass bound, unconditionally.** For every nonempty backward-closed `A` and `0 < λ ≤ 100/203 = 0.4926108…` there are `K > 0` and `x₀` with `Σ_{n ∈ A, n ≤ x} 1/n ≥ K (log x)^λ` for all `x ≥ x₀`. This is Theorem 5.3 of Paper C at an exponent above its `λ** ≈ 0.4925715`, and with the hypothesis removed. What leaves the critical path is Proposition 4.4 and its two exponential-sum bounds -- the manuscript's largest unformalized gap -- together with the six-word ladder and Appendix D. Compare `logMass_contagion_elementary`, which is unconditional at `13/40 = 0.325` because it pays Lemma 4.2's pointwise `2/9`; the whole gain is that the poor fibres have finite total logarithmic mass, so the coefficient may be averaged instead.

```lean
theorem logMass_contagion_averaged {A : ℕ → Prop} (hA : BackwardClosed A) {a : ℕ}
    (ha : 1 ≤ a) (hAa : A a) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam ≤ 100 / 203) :
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → K * Real.log x ^ lam ≤ logMass A x
```

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `family_OE_averaged`, `production_two_averaged`, `contagion_averaged`, `zeta2avg_pos`, `logMass_contagion_averaged`, `conjecture_of_tao_rate_averaged`, `conjecture_of_cylinder_averaged`*

*Runners-up: `production_two_averaged` (0.132), `logMass_contagion_averaged` (0.131)*

*If this row describes a definition rather than a theorem: `errAddAvg`, `errOEavg`*

## 53. `J-survivor-count-is-the-certificate-tail`

**Row.** PROVED IN LEAN, for every pair d <= K, over the naturals: 2^(K-d) * N_d = sum_{j=d+1}^{K} 2^(K-j) * M_j + N_K, where N_d = neverNegCount d counts the length-d words with no contracting prefix and M_j = minimalCertCount j counts those contracting for the first time at j. Divided by 2^K it reads N_d/2^d = sum_{j=d+1}^{K} M_j/2^j + N_K/2^K, 

**Candidate.** `neverNegCount_telescope` &mdash; kernel-checked, `formal/Problems/Juggler/PaperBCertificateRecursion.lean:362`

> **The telescoping identity.** For `d ≤ K`, `2 ^ (K - d) · N_d = Σ_{j = d+1}^{K} 2 ^ (K - j) · M_j + N_K`. It is `neverNegCount_add_minimalCertCount` summed and nothing else.

```lean
theorem neverNegCount_telescope {d K : ℕ} (h : d ≤ K) :
    2 ^ (K - d) * neverNegCount d
      = (∑ j ∈ Finset.Ico (d + 1) (K + 1), 2 ^ (K - j) * minimalCertCount j)
        + neverNegCount K
```

**Jev.** picks `neverNegCount_telescope` as well, at 0.99.

*The scorer rated this row low; it is listed on Jev's confidence.*

*Statement names: `neverNegCount_add_minimalCertCount`, `neverNegCount_telescope`, `minimalCert_tail_eq`*

*Runners-up: `neverNegCount_add_minimalCertCount` (0.099), `minimalCert_tail_eq` (0.094)*

*If this row describes a definition rather than a theorem: `minimalCertCount`, `minimalCertWords`*

## 54. `J-free-lengths-are-never-adjacent`

**Row.** PROVED IN LEAN, at every level: above the bottom edge, no two adjacent lengths are both free. carrying_in_adjacent_pair says that for floor(Lambda) + 1 <= L, at least one of L and L+1 carries a window at level 2^Lambda. MECHANISM. The carrying lengths are floor(o log2 3 + Lambda) + 1 (certWindowAt_iff_floor). Since 1 < log2 3 < 2, one ste

**Candidate.** `carrying_in_adjacent_pair` &mdash; kernel-checked, `formal/Problems/Juggler/PaperBLevelWindow.lean:805`

> **No two adjacent lengths are both free.** Above the bottom edge `⌊Λ⌋ + 1`, at least one of `L` and `L + 1` carries a window. The proof takes the least `o` whose boundary value reaches `L - 1`. If it is `0` the bottom-edge hypothesis pins it at `L - 1` exactly; otherwise its predecessor fell short, and one step moves the floor by at most `2`, so the value lands on `L - 1` or `L`.

```lean
theorem carrying_in_adjacent_pair {Λ : ℝ} (hΛ : 0 ≤ Λ) {L : ℕ} (hL : ⌊Λ⌋ + 1 ≤ (L : ℤ)) :
    (∃ o, CertWindowAt ((2 : ℝ) ^ Λ) L o) ∨ (∃ o, CertWindowAt ((2 : ℝ) ^ Λ) (L + 1) o)
```

**Jev.** picks `carrying_in_adjacent_pair` as well, at 0.92.

*Statement names: `carrying_in_adjacent_pair`, `certWindowAt_iff_floor`, `floor_step_bounds`, `not_cylinder_twice`*

*Runners-up: `certWindowAt_iff_floor` (0.088), `aliveWordsAt_succ_iff_window_empty` (0.082)*

*If this row describes a definition rather than a theorem: `CertWindowAt`, `minimalCertWordsAt`*

