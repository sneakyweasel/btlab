import Problems.Juggler.BeattyIsoBounds

/-!
# The Frostman bound at isolated slopes

The grid tree of an isolated slope carries a Cantor measure. If its window masses
satisfy `M_(j+1) ≤ Q_j^(-1 + η)` from some level on, then, combined with the
atom-mass bounds of `BeattyIsoBounds`, the Frostman inequality
`h(v) - h(u) ≤ C inc(u,v)^s` holds whenever

* `γ - 1 + η ≤ ν (1 - 3s/2)` (small scales), and
* `s (3 + ν - γ)/2 ≤ 1 - η` (chain scales).

The Frostman principle then gives `H^s(K_α) > 0`. Sparse good levels give
`M_(j+1) ≤ Q_j^(-1 + γ/(j+1))`, hence every `η > 0` from some level on.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set BeattyPhase

namespace IsoLevels

variable {ν γ B : ℝ} {G : ℕ → Prop} [DecidablePred G] {Lv : IsoLevels ν G B}
  (P : IsoParams ν γ B)

include P

/-- A child mass is at most `2 M / (d q)`. -/
theorem mass_step (L : ℕ) :
    (Lv.grid P).tree.mass (L + 1) ≤
      2 * (Lv.grid P).tree.mass L / ((Lv.grid P).d L * (Lv.grid P).q (L + 1)) := by
  set D := Lv.grid P
  have h := D.tree.mass_succ L
  have hN : D.d L * D.q (L + 1) / 2 ≤ D.tree.N L := D.nChild_ge_half L
  have hdq : 0 < D.d L * D.q (L + 1) := mul_pos (D.d_pos L) (D.qR_pos L)
  have hm := D.tree.mass_pos (L + 1)
  rw [le_div_iff₀ hdq]
  nlinarith

omit P in
/-- The denominator preceding a good level: `1` at level `0`, then `Q'_(j-1)`. -/
noncomputable def prevDen (Lv : IsoLevels ν G B) : ℕ → ℝ
  | 0 => 1
  | j + 1 => Lv.den' j

/-- The preceding denominator is positive and at most `Q'_j`. -/
theorem prevDen_bounds (j : ℕ) : 0 < prevDen Lv j ∧ prevDen Lv j ≤ Lv.den' j := by
  cases j with
  | zero =>
    exact ⟨one_pos, (den_one (Lv := Lv) P 0).trans (Lv.den_le_den' 0)⟩
  | succ j =>
    exact ⟨den'_pos (Lv := Lv) P j, (Lv.den'_le_den j).trans (Lv.den_le_den' (j + 1))⟩

/-- **Mass invariant.** `M_(j+1) Q_j ≤ (2 Y_j)^((j+1)γ)`, `Y_j` the preceding
denominator. -/
theorem mass_prevDen (j : ℕ) :
    (Lv.grid P).tree.mass (j + 1) * Lv.den j ≤
      (2 * prevDen Lv j) ^ (((j : ℝ) + 1) * γ) := by
  set D := Lv.grid P
  have hγ1 := P.γ1
  induction j with
  | zero =>
    have h := mass_step (Lv := Lv) P 0
    have h0 : D.tree.mass 0 = 1 := rfl
    have hd0 : D.d 0 = 1 := rfl
    have hq1 : (D.q 1 : ℝ) = Lv.den 0 := rfl
    rw [h0, hd0, hq1, one_mul, mul_one] at h
    have hq := den_pos (Lv := Lv) P 0
    have h2 : D.tree.mass 1 * Lv.den 0 ≤ 2 := by
      rwa [le_div_iff₀ hq] at h
    have : (2 : ℝ) ≤ (2 * prevDen Lv 0) ^ ((((0 : ℕ) : ℝ) + 1) * γ) := by
      simp only [prevDen, mul_one, Nat.cast_zero, zero_add, one_mul]
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ 2 ^ γ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1.le
    linarith
  | succ j ih =>
    have h := mass_step (Lv := Lv) P (j + 1)
    have hd : D.d (j + 1) = Lv.den j ^ (-γ) := rfl
    have hq2 : (D.q (j + 2) : ℝ) = Lv.den (j + 1) := rfl
    rw [hd, hq2] at h
    have hq := den_pos (Lv := Lv) P j
    have hq1 := den_pos (Lv := Lv) P (j + 1)
    have hq0 := den_one (Lv := Lv) P j
    have hdp : 0 < Lv.den j ^ (-γ) := Real.rpow_pos_of_pos hq _
    obtain ⟨hY0, hY1⟩ := prevDen_bounds (Lv := Lv) P j
    have hq' := den'_pos (Lv := Lv) P j
    have hM := D.tree.mass_pos (j + 1)
    -- `M_(j+2) Q_(j+1) ≤ 2 Q_j^(γ-1) (M_(j+1) Q_j)`
    have hinv : Lv.den j ^ (-γ) * Lv.den j ^ (γ - 1) * Lv.den j = 1 := by
      rw [← Real.rpow_add hq, ← Real.rpow_add_one hq.ne',
        show -γ + (γ - 1) + 1 = (0 : ℝ) by ring, Real.rpow_zero]
    have h1 : D.tree.mass (j + 2) * Lv.den (j + 1) ≤
        2 * Lv.den j ^ (γ - 1) * (D.tree.mass (j + 1) * Lv.den j) := by
      rw [le_div_iff₀ (mul_pos hdp hq1)] at h
      have : D.tree.mass (j + 2) * Lv.den (j + 1) * (Lv.den j ^ (-γ)) ≤
          2 * D.tree.mass (j + 1) := by nlinarith
      calc D.tree.mass (j + 2) * Lv.den (j + 1)
          = D.tree.mass (j + 2) * Lv.den (j + 1) * (Lv.den j ^ (-γ) * Lv.den j ^ (γ - 1) *
              Lv.den j) := by rw [hinv, mul_one]
        _ = (D.tree.mass (j + 2) * Lv.den (j + 1) * Lv.den j ^ (-γ)) *
              (Lv.den j ^ (γ - 1) * Lv.den j) := by ring
        _ ≤ (2 * D.tree.mass (j + 1)) * (Lv.den j ^ (γ - 1) * Lv.den j) :=
              mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    -- `2 Q_j^(γ-1) ≤ (2 Q'_j)^γ`
    have h2 : 2 * Lv.den j ^ (γ - 1) ≤ (2 * Lv.den' j) ^ γ := by
      rw [Real.mul_rpow (by norm_num) hq'.le]
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ γ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1.le
      · calc Lv.den j ^ (γ - 1) ≤ Lv.den j ^ γ :=
              Real.rpow_le_rpow_of_exponent_le hq0 (by linarith)
          _ ≤ Lv.den' j ^ γ := Real.rpow_le_rpow hq.le (Lv.den_le_den' j) (by linarith)
    have h3 : (2 * prevDen Lv j) ^ (((j : ℝ) + 1) * γ) ≤
        (2 * Lv.den' j) ^ (((j : ℝ) + 1) * γ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have h4 : (2 * Lv.den' j) ^ γ * (2 * Lv.den' j) ^ (((j : ℝ) + 1) * γ) =
        (2 * prevDen Lv (j + 1)) ^ ((((j + 1 : ℕ) : ℝ) + 1) * γ) := by
      rw [← Real.rpow_add (by positivity)]
      simp only [prevDen]
      push_cast; ring_nf
    rw [← h4]
    calc D.tree.mass (j + 1 + 1) * Lv.den (j + 1)
        ≤ 2 * Lv.den j ^ (γ - 1) * (D.tree.mass (j + 1) * Lv.den j) := h1
      _ ≤ (2 * Lv.den' j) ^ γ * (2 * Lv.den' j) ^ (((j : ℝ) + 1) * γ) :=
          mul_le_mul h2 (ih.trans h3) (by positivity) (by positivity)

/-- **Sparse masses.** From level `1` on, `M_(j+1) ≤ Q_j^(-1 + γ/(j+1))`. -/
theorem mass_sparse (hS : Lv.Sparse) {j : ℕ} (hj : 1 ≤ j) :
    (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ (-1 + γ / ((j : ℝ) + 1)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hq := den_pos (Lv := Lv) P (i + 1)
  have hγ := P.γ1
  have hM := mass_prevDen (Lv := Lv) P (i + 1)
  have hsp := hS i
  have hY : prevDen Lv (i + 1) = isoDen ν G (Lv.g i + 1) := rfl
  have hY0 := (prevDen_bounds (Lv := Lv) P (i + 1)).1
  have hn : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) + 1 := by positivity
  -- `(2Y)^((j+1)γ) = ((2Y)^((j+1)²))^(γ/(j+1)) ≤ Q_j^(γ/(j+1))`
  have hpow : (2 * prevDen Lv (i + 1)) ^ ((((i + 1 : ℕ) : ℝ) + 1) * γ) ≤
      Lv.den (i + 1) ^ (γ / (((i + 1 : ℕ) : ℝ) + 1)) := by
    have e : (2 * prevDen Lv (i + 1)) ^ ((((i + 1 : ℕ) : ℝ) + 1) * γ) =
        ((2 * prevDen Lv (i + 1)) ^ ((i + 2) ^ 2 : ℕ)) ^ (γ / (((i + 1 : ℕ) : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; field_simp; ring
    rw [e]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [hY]; unfold den; exact hsp
  have := hM.trans hpow
  rw [← le_div_iff₀ hq] at this
  calc (Lv.grid P).tree.mass (i + 1 + 1) ≤
      Lv.den (i + 1) ^ (γ / (((i + 1 : ℕ) : ℝ) + 1)) / Lv.den (i + 1) := this
    _ = Lv.den (i + 1) ^ (-1 + γ / (((i + 1 : ℕ) : ℝ) + 1)) := by
      rw [Real.rpow_add hq, Real.rpow_neg_one]; field_simp

/-- **Sparse masses beat every `η > 0`** from some level on. -/
theorem sparse_mass_eventually (hS : Lv.Sparse) {η : ℝ} (hη : 0 < η) :
    ∃ j0 : ℕ, ∀ j, j0 ≤ j → (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ (-1 + η) := by
  have hγ1 := P.γ1
  refine ⟨⌈γ / η⌉₊ + 1, fun j hj => ?_⟩
  have hj1 : 1 ≤ j := by omega
  have hc : γ / η ≤ ⌈γ / η⌉₊ := Nat.le_ceil _
  have hjR : ((⌈γ / η⌉₊ + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : γ / η ≤ (j : ℝ) + 1 := by push_cast at hjR; linarith
  have h2 : γ / ((j : ℝ) + 1) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hη] at h1
    linarith
  exact (mass_sparse (Lv := Lv) P hS hj1).trans
    (Real.rpow_le_rpow_of_exponent_le (den_one (Lv := Lv) P j) (by linarith))

/-- An interval meeting two children of a tree-level-`L` window has length at
least `1/(4 Q_L)`, and the Frostman left side is at most `9 M_(L+1) ℓ Q_L`. -/
theorem gap_width (L : ℕ) {a u v : ℝ} {m m' : ℕ} (hmm : m < m')
    (h1 : u < (Lv.grid P).tree.child L a m + (Lv.grid P).tree.d (L + 1))
    (h2 : (Lv.grid P).tree.child L a m' < v) :
    1 / 4 ≤ (v - u) * Lv.den L ∧
      (Lv.grid P).tree.mass (L + 1) * ((v - u) / (Lv.grid P).tree.sp L + 2) ≤
        9 * (Lv.grid P).tree.mass (L + 1) * ((v - u) * Lv.den L) := by
  set D := Lv.grid P
  have hq := den_pos (Lv := Lv) P L
  have hsp : D.tree.sp L = 1 / Lv.den L := rfl
  have hd : D.tree.d (L + 1) = Lv.den L ^ (-γ) := rfl
  have hmarg := (margins (Lv := Lv) P L).1
  have hq' : 0 < 2 / Lv.den' L := by have := den'_pos (Lv := Lv) P L; positivity
  have hgap : D.tree.child L a m + 1 / Lv.den L ≤ D.tree.child L a m' := by
    unfold WindowTree.child
    rw [hsp]
    have : ((m : ℕ) : ℝ) + 1 ≤ m' := by exact_mod_cast hmm
    have : 0 < 1 / Lv.den L := by positivity
    nlinarith
  rw [hd] at h1
  have hw : 1 / 4 / Lv.den L ≤ v - u := by
    have : 1 / Lv.den L = 1 / 4 / Lv.den L + 3 / 4 / Lv.den L := by ring
    linarith
  have hw' : 1 / 4 ≤ (v - u) * Lv.den L := by
    rw [div_div, div_le_iff₀ (by positivity)] at hw; linarith
  refine ⟨hw', ?_⟩
  have hM := D.tree.mass_pos (L + 1)
  rw [hsp, div_div_eq_mul_div, div_one]
  nlinarith

/-- **Small-scale exponent.** If `M ≤ Q^(-1+η)`, `ℓ Q' ≤ 10` and
`γ - 1 + η ≤ ν(1 - 3s/2)`, then `18 M ℓ Q^γ ≤ 180 ℓ^(3s/2)`. -/
theorem small_exponent (j : ℕ) {s η M ℓ : ℝ} (hs : 0 < s) (hs23 : s < 2 / 3)
    (hE1 : γ - 1 + η ≤ ν * (1 - 3 * s / 2)) (_hM0 : 0 ≤ M)
    (hM : M ≤ Lv.den j ^ (-1 + η)) (hℓ : 0 < ℓ) (hℓQ : ℓ * Lv.den' j ≤ 10) :
    18 * M * ℓ / Lv.den j ^ (-γ) ≤ 180 * ℓ ^ (3 * s / 2) := by
  have hq := den_pos (Lv := Lv) P j
  have hq1 := den_one (Lv := Lv) P j
  have hν1 : 1 ≤ ν := by linarith [P.γ1, P.γν]
  have hq' := den'_pos (Lv := Lv) P j
  set p := 1 - 3 * s / 2 with hp
  have hp0 : 0 ≤ p := by linarith
  have hp1 : p ≤ 1 := by linarith
  -- `ℓ^p ≤ 10 Q^(-νp)`
  have hℓp : ℓ ^ p ≤ 10 * Lv.den j ^ (-(ν * p)) := by
    have hle : ℓ ≤ 10 / Lv.den j ^ ν := by
      rw [le_div_iff₀ (by positivity)]
      have := (Lv.den'_bounds hν1 j).1
      nlinarith
    calc ℓ ^ p ≤ (10 / Lv.den j ^ ν) ^ p := Real.rpow_le_rpow hℓ.le hle hp0
      _ = 10 ^ p * Lv.den j ^ (-(ν * p)) := by
          rw [Real.div_rpow (by norm_num) (by positivity), ← Real.rpow_mul hq.le,
            Real.rpow_neg hq.le, div_eq_mul_inv]
      _ ≤ 10 * Lv.den j ^ (-(ν * p)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (10 : ℝ) ^ p ≤ 10 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
            _ = 10 := Real.rpow_one 10
  have hexp : Lv.den j ^ (-1 + η) * Lv.den j ^ γ * Lv.den j ^ (-(ν * p)) ≤ 1 := by
    rw [← Real.rpow_add hq, ← Real.rpow_add hq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hsplit : ℓ = ℓ ^ (3 * s / 2) * ℓ ^ p := by
    rw [← Real.rpow_add hℓ, hp, show 3 * s / 2 + (1 - 3 * s / 2) = (1 : ℝ) by ring,
      Real.rpow_one]
  have hinv : 1 / Lv.den j ^ (-γ) = Lv.den j ^ γ := by
    rw [Real.rpow_neg hq.le, one_div, inv_inv]
  have hl32 : 0 ≤ ℓ ^ (3 * s / 2) := by positivity
  calc 18 * M * ℓ / Lv.den j ^ (-γ) = 18 * ℓ ^ (3 * s / 2) * (M * Lv.den j ^ γ * ℓ ^ p) := by
        rw [div_eq_mul_one_div, hinv]; nth_rewrite 1 [hsplit]; ring
    _ ≤ 18 * ℓ ^ (3 * s / 2) *
          (Lv.den j ^ (-1 + η) * Lv.den j ^ γ * (10 * Lv.den j ^ (-(ν * p)))) := by
        gcongr
    _ = 180 * ℓ ^ (3 * s / 2) *
          (Lv.den j ^ (-1 + η) * Lv.den j ^ γ * Lv.den j ^ (-(ν * p))) := by ring
    _ ≤ 180 * ℓ ^ (3 * s / 2) * 1 := by gcongr
    _ = 180 * ℓ ^ (3 * s / 2) := mul_one _

/-- **Chain scale.** Inside a charged window of good level `j`, an interval of
length `ℓ ≥ 10/Q'_j` has atom mass at least `(A/32) (ℓ/d) / Q^((3+ν-γ)/2)`. -/
theorem chain_scale (j : ℕ) {a u v : ℝ} (ha : (Lv.grid P).tree.Charged (j + 1) a)
    (hu : a ≤ u) (huv : u < v) (hv : v ≤ a + Lv.den j ^ (-γ))
    (hw : 10 ≤ (v - u) * Lv.den' j) {A : ℝ} (hA : 0 < A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k) :
    A / 32 * ((v - u) / Lv.den j ^ (-γ)) / Lv.den j ^ ((3 + ν - γ) / 2) ≤ inc ν G u v := by
  refine le_trans ?_ (chain_window (Lv := Lv) P j ha hu huv hv (by linarith) hA hwA)
  have hq := den_pos (Lv := Lv) P j
  have hq' := den'_pos (Lv := Lv) P j
  have hν1 : 1 ≤ ν := by linarith [P.γ1, P.γν]
  set d := Lv.den j ^ (-γ) with hd
  have hdp : 0 < d := Real.rpow_pos_of_pos hq _
  set X := d * Lv.den' j with hX
  have hXp : 0 < X := by positivity
  have hℓ : 0 < v - u := by linarith
  -- `X ≤ 4 Q^(ν-γ)`, so `X^(1/2) ≤ 2 Q^((ν-γ)/2)`
  have hXle : X ≤ 4 * Lv.den j ^ (ν - γ) := by
    have := (Lv.den'_bounds hν1 j).2
    calc X ≤ d * (4 * Lv.den j ^ ν) := mul_le_mul_of_nonneg_left this hdp.le
      _ = 4 * Lv.den j ^ (ν - γ) := by
          rw [hd, sub_eq_add_neg, Real.rpow_add hq]; ring
  have hsq : X ^ (1/2 : ℝ) ≤ 2 * Lv.den j ^ ((ν - γ) / 2) := by
    calc X ^ (1/2 : ℝ) ≤ (4 * Lv.den j ^ (ν - γ)) ^ (1/2 : ℝ) :=
          Real.rpow_le_rpow hXp.le hXle (by norm_num)
      _ = 2 * Lv.den j ^ ((ν - γ) / 2) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hq.le,
            show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num; ring_nf
  -- `(4 X Q)^(3/2) = 8 X X^(1/2) Q^(3/2)`
  have h32 : (4 * d * Lv.den' j * Lv.den j) ^ (3/2 : ℝ) =
      8 * X * X ^ (1/2 : ℝ) * Lv.den j ^ (3/2 : ℝ) := by
    rw [show 4 * d * Lv.den' j * Lv.den j = 4 * X * Lv.den j by rw [hX]; ring,
      Real.mul_rpow (by positivity) hq.le, Real.mul_rpow (by norm_num) hXp.le,
      show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hXp, Real.rpow_one,
      Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
    norm_num
    left; ring
  have hQe : Lv.den j ^ ((3 + ν - γ) / 2) = Lv.den j ^ ((ν - γ) / 2) * Lv.den j ^ (3/2 : ℝ) := by
    rw [← Real.rpow_add hq]; ring_nf
  rw [h32, hQe]
  have hs0 : 0 < X ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hQ32 : 0 < Lv.den j ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hq _
  have hQν : 0 < Lv.den j ^ ((ν - γ) / 2) := Real.rpow_pos_of_pos hq _
  -- both sides as `(A (v-u) / d) / (...)`
  have e1 : (v - u) * Lv.den' j / 2 * (A / (8 * X * X ^ (1/2 : ℝ) * Lv.den j ^ (3/2 : ℝ))) =
      A * ((v - u) / d) / (16 * X ^ (1/2 : ℝ) * Lv.den j ^ (3/2 : ℝ)) := by
    rw [hX]; field_simp; ring
  have e2 : A / 32 * ((v - u) / d) / (Lv.den j ^ ((ν - γ) / 2) * Lv.den j ^ (3/2 : ℝ)) =
      A * ((v - u) / d) / (32 * (Lv.den j ^ ((ν - γ) / 2) * Lv.den j ^ (3/2 : ℝ))) := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-- **Chain-scale exponent.** If `M ≤ Q^(-1+η)`, `ℓ ≤ d`, and
`s(3+ν-γ)/2 ≤ 1 - η`, then `18 M ℓ/d ≤ 18 (32/A)^s ((A/32)(ℓ/d)/Q^e)^s`. -/
theorem chain_exponent (j : ℕ) {s η M ℓ A : ℝ} (_hs : 0 < s) (hs1 : s ≤ 1)
    (hE2 : s * (3 + ν - γ) / 2 ≤ 1 - η) (hM0 : 0 ≤ M) (hM : M ≤ Lv.den j ^ (-1 + η))
    (hℓ : 0 < ℓ) (hℓd : ℓ ≤ Lv.den j ^ (-γ)) (hA : 0 < A) :
    18 * M * ℓ / Lv.den j ^ (-γ) ≤
      18 * (32 / A) ^ s * (A / 32 * (ℓ / Lv.den j ^ (-γ)) / Lv.den j ^ ((3 + ν - γ) / 2)) ^ s := by
  have hq := den_pos (Lv := Lv) P j
  have hq1 := den_one (Lv := Lv) P j
  set d := Lv.den j ^ (-γ)
  have hdp : 0 < d := Real.rpow_pos_of_pos hq _
  set e := (3 + ν - γ) / 2
  set x := ℓ / d with hx
  have hx0 : 0 < x := div_pos hℓ hdp
  have hx1 : x ≤ 1 := (div_le_one hdp).2 hℓd
  have hxs : x ≤ x ^ s := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ s := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hs1
  have hQe : 0 < Lv.den j ^ e := Real.rpow_pos_of_pos hq _
  -- `M (Q^e)^s ≤ 1`
  have hMQ : M * (Lv.den j ^ e) ^ s ≤ 1 := by
    rw [← Real.rpow_mul hq.le]
    calc M * Lv.den j ^ (e * s) ≤ Lv.den j ^ (-1 + η) * Lv.den j ^ (e * s) :=
          mul_le_mul_of_nonneg_right hM (by positivity)
      _ = Lv.den j ^ (-1 + η + e * s) := (Real.rpow_add hq _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by simp only [e]; nlinarith)
  have hA32 : (32 / A) ^ s * (A / 32) ^ s = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show 32 / A * (A / 32) = 1 by field_simp, Real.one_rpow]
  have hrhs : (A / 32 * x / Lv.den j ^ e) ^ s = (A / 32) ^ s * x ^ s / (Lv.den j ^ e) ^ s := by
    rw [Real.div_rpow (by positivity) hQe.le, Real.mul_rpow (by positivity) hx0.le]
  have hQes : 0 < (Lv.den j ^ e) ^ s := Real.rpow_pos_of_pos hQe _
  rw [hrhs]
  calc 18 * M * ℓ / d = 18 * M * x := by rw [hx]; ring
    _ ≤ 18 * M * x ^ s := by gcongr
    _ = 18 * (M * (Lv.den j ^ e) ^ s) * (x ^ s / (Lv.den j ^ e) ^ s) := by
        field_simp
    _ ≤ 18 * 1 * (x ^ s / (Lv.den j ^ e) ^ s) := by gcongr
    _ = 18 * ((32 / A) ^ s * (A / 32) ^ s) * (x ^ s / (Lv.den j ^ e) ^ s) := by rw [hA32]
    _ = _ := by ring

/-- **Frostman bound on the grid tree.** Under the two exponent conditions,
`h(v) - h(u) ≤ C inc(u,v)^s` on `[0, 1]`, for the limit distribution function
`h` of the grid tree. -/
theorem frostman_tree {s η : ℝ} (hs : 0 < s) (hs23 : s < 2 / 3) (j0 : ℕ)
    (hM : ∀ j, j0 ≤ j → (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ (-1 + η))
    (hE1 : γ - 1 + η ≤ ν * (1 - 3 * s / 2)) (hE2 : s * (3 + ν - γ) / 2 ≤ 1 - η) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
      (Lv.grid P).tree.hlim v - (Lv.grid P).tree.hlim u ≤ C * inc ν G u v ^ s := by
  classical
  set D := Lv.grid P
  set T := D.tree
  obtain ⟨A, hA, hwA⟩ := wt_lower (ν := ν) (G := G)
  have hγ1 := P.γ1
  have hQ0 := den_pos (Lv := Lv) P j0
  set c0 := A / Lv.den j0 ^ (3/2 : ℝ) with hc0
  have hc0p : 0 < c0 := by positivity
  set c1 := A / 20 ^ (3/2 : ℝ) with hc1
  have hc1p : 0 < c1 := by positivity
  set C0 := 9 * Lv.den j0 / c0 ^ s
  set C1 := 180 / c1 ^ s
  set C2 := 18 * (32 / A) ^ s
  have hC0 : 0 < C0 := by positivity
  have hC1 : 0 < C1 := by positivity
  have hC2 : 0 < C2 := by positivity
  refine ⟨C0 + C1 + C2, by positivity, ?_⟩
  have hup : ∀ Ci x : ℝ, 0 ≤ x → Ci ≤ C0 + C1 + C2 → Ci * x ^ s ≤ (C0 + C1 + C2) * x ^ s :=
    fun Ci x hx h => mul_le_mul_of_nonneg_right h (by positivity)
  intro u v hu huv hv
  have hd0 : T.d 0 = 1 := rfl
  refine T.descent (Φ := fun u v => inc ν G u v) (by positivity) hs
    (fun u v h => inc_nonneg h) (fun u v u' v' h1 h2 h3 => inc_mono h1 h2 h3) ?_ u v hu huv
    (by rw [hd0]; exact hv)
  intro l a u v hch hau huv hva hcard
  -- two children meeting `(u, v)`
  obtain ⟨m1, hm1, m2, hm2, hne⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two hcard)
  simp only [Finset.mem_filter, Finset.mem_range] at hm1 hm2
  obtain ⟨m, m', hmm, hm', h1, h2⟩ : ∃ m m', m < m' ∧ m' < T.N l ∧
      u < T.child l a m + T.d (l + 1) ∧ T.child l a m' < v := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨m1, m2, h, hm2.1, hm1.2.2, hm2.2.1⟩
    · exact ⟨m2, m1, h, hm1.1, hm2.2.2, hm1.2.1⟩
  obtain ⟨ha0, ha1⟩ := D.charged_unit l a hch
  have hu0 : 0 ≤ u := ha0.trans hau
  have hdl := D.d_pos l
  have hv1 : v ≤ 1 := by
    have : v ≤ a + D.d l := hva
    linarith
  obtain ⟨hwidth, hlhs⟩ := gap_width (Lv := Lv) P l hmm h1 h2
  have hinc0 := inc_nonneg (ν := ν) (G := G) huv
  by_cases hl : l ≤ j0
  · -- low levels: a constant bound
    have hbase := base_between (Lv := Lv) P l hch hmm hm' h1 h2 hA hwA
    have hql : Lv.den l ≤ Lv.den j0 := Lv.den_mono hl
    have hql0 := den_pos (Lv := Lv) P l
    have hc0le : c0 ≤ inc ν G u v := by
      refine le_trans ?_ hbase
      apply div_le_div_of_nonneg_left hA.le (by positivity)
      exact Real.rpow_le_rpow hql0.le hql (by norm_num)
    have hmass : T.mass (l + 1) ≤ 1 := by
      have := T.mass_le_pow 0 (l + 1)
      rw [zero_add] at this
      have h0 : T.mass 0 = 1 := rfl
      rw [h0, one_mul] at this
      exact this.trans (pow_le_one₀ (by norm_num) (by norm_num))
    have hℓ : v - u ≤ 1 := by linarith
    have hM0 := T.mass_pos (l + 1)
    calc T.mass (l + 1) * ((v - u) / T.sp l + 2)
        ≤ 9 * T.mass (l + 1) * ((v - u) * Lv.den l) := hlhs
      _ ≤ 9 * 1 * (1 * Lv.den j0) := by gcongr
      _ = C0 * c0 ^ s := by
          have : 0 < c0 ^ s := by positivity
          rw [show C0 = 9 * Lv.den j0 / c0 ^ s from rfl, div_mul_cancel₀ _ this.ne']; ring
      _ ≤ C0 * inc ν G u v ^ s := by
          gcongr
      _ ≤ (C0 + C1 + C2) * inc ν G u v ^ s := hup _ _ hinc0 (by linarith)
  · -- high levels `l = j + 1`
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    have hq := den_pos (Lv := Lv) P j
    have hq1 := den_one (Lv := Lv) P j
    have hq2 := den_pos (Lv := Lv) P (j + 1)
    set M := T.mass (j + 1)
    have hM0 : 0 < M := T.mass_pos _
    have hMη : M ≤ Lv.den j ^ (-1 + η) := hM j (by omega)
    set d := Lv.den j ^ (-γ)
    have hdp : 0 < d := Real.rpow_pos_of_pos hq _
    have hDd : D.d (j + 1) = d := rfl
    -- the left side is at most `18 M ℓ / d`
    have hstep := mass_step (Lv := Lv) P (j + 1)
    have hq2' : (D.q (j + 1 + 1) : ℝ) = Lv.den (j + 1) := rfl
    rw [hDd, hq2'] at hstep
    have hℓ : 0 < v - u := by linarith
    have hlhs' : T.mass (j + 1 + 1) * ((v - u) / T.sp (j + 1) + 2) ≤ 18 * M * (v - u) / d := by
      refine hlhs.trans ?_
      have hmd : T.mass (j + 1 + 1) * (d * Lv.den (j + 1)) ≤ 2 * M := by
        rwa [le_div_iff₀ (by positivity)] at hstep
      rw [le_div_iff₀ hdp]
      nlinarith
    refine hlhs'.trans ?_
    have hva' : v ≤ a + d := hva
    by_cases hsc : (v - u) * Lv.den' j ≤ 10
    · have hsm := small_scale (Lv := Lv) P j hch hmm hm' h1 h2 hu0 huv hv1 hsc hA hwA
      have hexp := small_exponent (Lv := Lv) P j hs hs23 hE1 hM0.le hMη hℓ hsc
      have hlow : (A * (v - u) ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ)) ^ s =
          c1 ^ s * (v - u) ^ (3 * s / 2) := by
        rw [show A * (v - u) ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ) = c1 * (v - u) ^ (3/2 : ℝ) by
              rw [hc1]; ring,
          Real.mul_rpow hc1p.le (by positivity), ← Real.rpow_mul hℓ.le]
        ring_nf
      calc 18 * M * (v - u) / d ≤ 180 * (v - u) ^ (3 * s / 2) := hexp
        _ = C1 * (A * (v - u) ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ)) ^ s := by
            rw [hlow]
            have : 0 < c1 ^ s := by positivity
            rw [show C1 = 180 / c1 ^ s from rfl, ← mul_assoc, div_mul_cancel₀ _ this.ne']
        _ ≤ C1 * inc ν G u v ^ s := by
            gcongr
        _ ≤ (C0 + C1 + C2) * inc ν G u v ^ s := hup _ _ hinc0 (by linarith)
    · have hch' := chain_scale (Lv := Lv) P j hch hau huv hva' (by linarith) hA hwA
      have hℓd : v - u ≤ d := by linarith
      have hexp := chain_exponent (Lv := Lv) P j hs (by linarith) hE2 hM0.le hMη hℓ hℓd hA
      calc 18 * M * (v - u) / d ≤ C2 *
            (A / 32 * ((v - u) / d) / Lv.den j ^ ((3 + ν - γ) / 2)) ^ s := hexp
        _ ≤ C2 * inc ν G u v ^ s := by
            gcongr
        _ ≤ (C0 + C1 + C2) * inc ν G u v ^ s := hup _ _ hinc0 (by linarith)

/-- **Positive Hausdorff measure.** Under the exponent conditions, the cluster
set of the isolated slope has positive `s`-dimensional Hausdorff measure. -/
theorem hausdorff_ne_zero (Lv : IsoLevels ν G B) {s η : ℝ} (hs : 0 < s) (hs23 : s < 2 / 3)
    (j0 : ℕ) (hM : ∀ j, j0 ≤ j → (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ (-1 + η))
    (hE1 : γ - 1 + η ≤ ν * (1 - 3 * s / 2)) (hE2 : s * (3 + ν - γ) / 2 ≤ 1 - η) :
    MeasureTheory.Measure.hausdorffMeasure s (passageClusterSet (1 / isoSlope ν G)) ≠ 0 := by
  obtain ⟨C, hC, hfrost⟩ := frostman_tree (Lv := Lv) P hs hs23 j0 hM hE1 hE2
  obtain ⟨hβ0, hβ1, hβ⟩ := β_bounds (ν := ν) (G := G)
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  set T := (Lv.grid P).tree
  have hd0 : T.d 0 = 1 := rfl
  have hne : T.hlim 0 < T.hlim 1 := by
    rw [T.hlim_zero, ← hd0, T.hlim_top]; norm_num
  exact frostman_cdf_hausdorff (wt_summable (ν := ν) (G := G)) (wt_nonneg (ν := ν) (G := G))
    (ph_inj (ν := ν) (G := G)) (ph_mem (ν := ν) (G := G)) hs hC T.hlim T.hlim_mono
    T.hlim_cont hne hfrost

end IsoLevels

end Problems.Juggler.BeattySlope
