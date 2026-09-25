import Problems.Juggler.BeattyIsoGrid

/-!
# Atom-mass bounds on the grid tree of an isolated slope

For the rotation profile of the isolated slope `α` (phases `{(k+1)α}`, weights
the actual first-passage weights at `β = 1/α`):

* **base**: an interval meeting two children of a charged window of tree level
  `L` contains the base between them, of index below `Q_(g L)`, so its atom
  mass is at least `A Q_(g L)^(-3/2)`;
* **chain**: an interval of length at least `10/Q'` inside a charged window of
  good level `j` contains at least half of `ℓ Q'` chain atoms of index at most
  `4 d Q' Q`;
* **hits**: an interval of length between `20/Q_(g (j+1))` and `10/Q'_j` holds
  many atoms below a convergent `Q ≤ 20/ℓ`, so its mass is at least
  `(A/10) 20^(-1/2) ℓ^(3/2)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set BeattyPhase

namespace IsoLevels

variable {ν γ B : ℝ} {G : ℕ → Prop} [DecidablePred G] {Lv : IsoLevels ν G B}
  (P : IsoParams ν γ B)

include P

omit P in
/-- The isolated slope exceeds one. -/
theorem slope_gt : 1 < isoSlope ν G := one_lt_isoSlope ν G

omit P in
/-- The atom phases of the isolated slope. -/
noncomputable def ph (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (k : ℕ) : ℝ :=
  passagePhase (1 / isoSlope ν G) (k + 1)

omit P in
/-- The atom weights of the isolated slope. -/
noncomputable def wt (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (k : ℕ) : ℝ :=
  passageJumpWeight (1 / isoSlope ν G) (k + 1)

omit P in
/-- The passage parameter `β = 1/α` lies in `(0, 1)` and is irrational. -/
theorem β_bounds : 0 < 1 / isoSlope ν G ∧ 1 / isoSlope ν G < 1 ∧ Irrational (1 / isoSlope ν G) :=
  ⟨one_div_pos.2 (by linarith [one_lt_isoSlope ν G]),
    (div_lt_one (by linarith [one_lt_isoSlope ν G])).2 (one_lt_isoSlope ν G),
    by simpa using (isoSlope_irrational ν G).inv⟩

omit P in
/-- The phase of index `k` is `{(k+1) α}`. -/
theorem ph_fract (k : ℕ) : ph ν G k = Int.fract (((k : ℝ) + 1) * isoSlope ν G) := by
  unfold ph
  rw [passagePhase_succ_fract (β_bounds (ν := ν) (G := G)).1, one_div_one_div]

omit P in
/-- The atom weights are summable. -/
theorem wt_summable : Summable (wt ν G) :=
  (passage_jump_weights_hasSum β_bounds.1 β_bounds.2.1 β_bounds.2.2).summable

omit P in
/-- The atom weights are nonnegative. -/
theorem wt_nonneg (k : ℕ) : 0 ≤ wt ν G k := passageJumpWeight_nonneg β_bounds.1 β_bounds.2.1 _

omit P in
/-- Distinct indices have distinct phases. -/
theorem ph_inj : Function.Injective (ph ν G) :=
  (passagePhase_injective β_bounds.1 β_bounds.2.1 β_bounds.2.2).comp (add_left_injective 1)

omit P in
/-- Every phase lies in the open unit interval. -/
theorem ph_mem (k : ℕ) : ph ν G k ∈ Ioo (0 : ℝ) 1 :=
  ⟨passagePhase_pos β_bounds.1 β_bounds.2.1 β_bounds.2.2 (Nat.succ_pos k),
    (passagePhase_mem_Ico β_bounds.1 _).2⟩

omit P in
/-- A lower weight constant. -/
theorem wt_lower : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k := by
  obtain ⟨A, B', hA, -, hw⟩ := passageWeight_three_halves β_bounds.1 β_bounds.2.1
    (β_bounds (ν := ν) (G := G)).2.2
  exact ⟨A, hA, fun k => (hw k).1⟩

/-- The atom mass of a phase interval. -/
noncomputable def inc (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (u v : ℝ) : ℝ :=
  jumpProfile (ph ν G) (wt ν G) v - jumpProfileRight (ph ν G) (wt ν G) u

omit P in
/-- The error at a good level is nonzero. -/
theorem θ_ne (l : ℕ) : Lv.θ l ≠ 0 := by
  intro h
  have := (Lv.θ_bounds l).1
  rw [h, abs_zero] at this
  have hq : 0 < Lv.den' l := by
    unfold den'; exact_mod_cast isoDen_pos (Lv.g l)
  have : 0 < 1 / (2 * Lv.den' l) := by positivity
  linarith

/-- The base at grid point `gp`, `0 < gp < q`, of good level `l`: an index
`0 < t < q` with `{tα} = gp/q + tθ/q`. -/
theorem base_exists (l : ℕ) {gp : ℕ} (hg1 : 1 ≤ gp) (hgq : gp < isoDen ν G (Lv.g l)) :
    ∃ t : ℕ, 1 ≤ t ∧ t < isoDen ν G (Lv.g l) ∧
      Int.fract ((t : ℝ) * isoSlope ν G) = (gp : ℝ) / Lv.den l + t * Lv.θ l / Lv.den l := by
  have hq1 : 1 < isoDen ν G (Lv.g l) := by
    have := Lv.den_ge l; have := P.B10
    have : (1 : ℝ) < isoDen ν G (Lv.g l) := by unfold den at *; linarith
    exact_mod_cast this
  have hcop := iso_isCoprime (ν := ν) (G := G) (Lv.g l) (Lv.one_le_g l)
  have hθ : |(isoDen ν G (Lv.g l) : ℝ) * isoSlope ν G - (cfNum (isoQuot ν G) (Lv.g l) : ℤ)| <
      1 / (isoDen ν G (Lv.g l) : ℝ) := by
    have h1 := (Lv.θ_bounds l).2
    have hq := den_pos (Lv := Lv) P l
    have hlt : Lv.den l < Lv.den' l := by
      have hν1 : 1 < ν := P.γ1.trans P.γν
      have := (Lv.den'_bounds hν1.le l).1
      have h8 : 8 ≤ Lv.den l ^ (ν - 1) := (den_rpow_γ (Lv := Lv) P l).trans
        (Real.rpow_le_rpow_of_exponent_le (den_one (Lv := Lv) P l) (by linarith [P.γν]))
      have : Lv.den l ^ ν = Lv.den l * Lv.den l ^ (ν - 1) := by
        rw [← Real.rpow_one_add' hq.le (by linarith)]; ring_nf
      nlinarith
    have : 1 / Lv.den' l < 1 / Lv.den l := one_div_lt_one_div_of_lt hq hlt
    unfold θ den at *
    push_cast at *
    linarith
  obtain ⟨t, h1, h2, h3⟩ := base_at_grid hq1 hcop hθ hg1 hgq
  exact ⟨t, h1, h2, by rw [h3]; unfold θ den; push_cast; ring⟩

/-- Sizes of the base shift: `0 < tθ/q < θ` on the positive side and
`θ < tθ/q < 0` on the negative side. -/
theorem shift_bounds (l : ℕ) {t : ℕ} (ht1 : 1 ≤ t) (htq : t < isoDen ν G (Lv.g l)) :
    |(t : ℝ) * Lv.θ l / Lv.den l| < |Lv.θ l| ∧
      (0 < Lv.θ l → 0 < (t : ℝ) * Lv.θ l / Lv.den l) ∧
      (Lv.θ l < 0 → (t : ℝ) * Lv.θ l / Lv.den l < 0) := by
  have hq := den_pos (Lv := Lv) P l
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have htq' : (t : ℝ) < Lv.den l := by unfold den; exact_mod_cast htq
  have hθ := θ_ne (Lv := Lv) l
  refine ⟨?_, fun h => by positivity, fun h => div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by linarith) h) hq⟩
  rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t), abs_of_pos hq,
    div_lt_iff₀ hq]
  have : 0 < |Lv.θ l| := abs_pos.2 hθ
  nlinarith

/-- **Base between children.** An interval meeting two children of a charged
window of tree level `L` has atom mass at least `A Q_(g L)^(-3/2)`. -/
theorem base_between (L : ℕ) {a u v : ℝ} (ha : (Lv.grid P).tree.Charged L a) {m m' : ℕ}
    (hmm : m < m') (hm' : m' < (Lv.grid P).tree.N L)
    (h1 : u < (Lv.grid P).tree.child L a m + (Lv.grid P).tree.d (L + 1))
    (h2 : (Lv.grid P).tree.child L a m' < v) {A : ℝ} (hA : 0 < A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k) :
    A / Lv.den L ^ (3/2 : ℝ) ≤ inc ν G u v := by
  set D := Lv.grid P
  obtain ⟨ha0, ha1⟩ := D.charged_unit L a ha
  have hqL : (D.q (L + 1) : ℝ) = Lv.den L := rfl
  have hq := den_pos (Lv := Lv) P L
  set i := ⌊a * D.q (L + 1)⌋₊ + 2 + m with hi
  have hcm : D.tree.child L a m = D.leftEnd (L + 1) i := D.tree_child L ha0 m
  have hcm1 : D.tree.child L a (m + 1) = D.leftEnd (L + 1) (i + 1) := by
    rw [D.tree_child L ha0 (m + 1)]; congr 1
  have hmono : D.tree.child L a (m + 1) ≤ D.tree.child L a m' := by
    unfold WindowTree.child
    have : ((m + 1 : ℕ) : ℝ) ≤ m' := by exact_mod_cast hmm
    have := D.tree.sp_pos L
    nlinarith
  -- the grid index bound `i + 1 ≤ q - 3`
  have hibound : (i : ℝ) + 1 + 3 ≤ Lv.den L := by
    have hfl : (⌊a * D.q (L + 1)⌋₊ : ℝ) ≤ a * D.q (L + 1) := Nat.floor_le (by positivity)
    have hN := D.nChild_le L
    have hm'N : (m' : ℝ) + 1 ≤ D.nChild L := by
      have : m' + 1 ≤ D.nChild L := hm'; exact_mod_cast this
    have hmm' : (m : ℝ) + 1 ≤ m' := by exact_mod_cast hmm
    have : (a + D.d L) * D.q (L + 1) ≤ D.q (L + 1) := by
      have := D.qR_pos L; nlinarith
    rw [← hqL]; simp only [hi]; push_cast; nlinarith
  have hd' : D.d (L + 1) = Lv.den L ^ (-γ) := rfl
  have hdt : D.tree.d (L + 1) = Lv.den L ^ (-γ) := rfl
  have hq' : D.q' (L + 1) = Lv.den' L := rfl
  obtain ⟨hmarg, -⟩ := margins (Lv := Lv) P L
  have hθb := (Lv.θ_bounds L).2
  have hθ := θ_ne (Lv := Lv) L
  have hden' : 0 < Lv.den' L := den'_pos (Lv := Lv) P L
  have hr : 0 < 1 / Lv.den' L := by positivity
  have hdp : 0 < Lv.den L ^ (-γ) := Real.rpow_pos_of_pos hq _
  -- choose the grid point next to the gap
  obtain ⟨gp, hg1, hgq, hbelow, habove⟩ : ∃ gp : ℕ, 1 ≤ gp ∧ gp < isoDen ν G (Lv.g L) ∧
      (∀ b : ℝ, |b - gp / Lv.den L| < |Lv.θ L| →
        (0 < Lv.θ L → gp / Lv.den L < b) → (Lv.θ L < 0 → b < gp / Lv.den L) →
        D.tree.child L a m + D.tree.d (L + 1) < b) ∧
      (∀ b : ℝ, |b - gp / Lv.den L| < |Lv.θ L| →
        (0 < Lv.θ L → gp / Lv.den L < b) → (Lv.θ L < 0 → b < gp / Lv.den L) →
        b < D.tree.child L a (m + 1)) := by
    have hdef : ((isoDen ν G (Lv.g L) : ℕ) : ℝ) = Lv.den L := rfl
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · -- negative side: the base of grid `i` lies right of child `m`
      have hs : Lv.side L = false := by simp [side, not_lt.2 hneg.le]
      have he : D.e (L + 1) = -(2 / Lv.den' L) - Lv.den L ^ (-γ) := by
        show (if D.pos (L + 1) then _ else _) = _
        simp only [D, grid, hs]; rfl
      refine ⟨i, by omega, ?_, ?_, ?_⟩
      · have : (i : ℝ) < isoDen ν G (Lv.g L) := by rw [hdef]; linarith
        exact_mod_cast this
      · intro b hb _ hb2
        rw [hcm]; simp only [GridData.leftEnd, hqL, he, hdt]
        rw [abs_lt] at hb; rw [abs_of_neg hneg] at hb hθb
        have : 1 / Lv.den' L < 2 / Lv.den' L := by
          rw [div_lt_div_iff_of_pos_right hden']; norm_num
        linarith [hb.1]
      · intro b _ _ hb2
        rw [hcm1]; simp only [GridData.leftEnd, hqL, he]
        have hb := hb2 hneg
        have : (i : ℝ) / Lv.den L + 1 / Lv.den L < ((i + 1 : ℕ) : ℝ) / Lv.den L -
            2 / Lv.den' L - Lv.den L ^ (-γ) + 1 / Lv.den L := by
          push_cast; rw [add_div]
          have : 2 / Lv.den' L + Lv.den L ^ (-γ) < 1 / Lv.den L := by
            have : 3 / 4 / Lv.den L < 1 / Lv.den L := div_lt_div_of_pos_right (by norm_num) hq
            linarith
          linarith
        push_cast at this ⊢; rw [add_div] at this ⊢; linarith
    · -- positive side: the base of grid `i + 1` lies right of child `m`
      have hs : Lv.side L = true := by simp [side, hpos]
      have he : D.e (L + 1) = 2 / Lv.den' L := by
        show (if D.pos (L + 1) then _ else _) = _
        simp only [D, grid, hs, if_true]
      refine ⟨i + 1, by omega, ?_, ?_, ?_⟩
      · have : ((i + 1 : ℕ) : ℝ) < isoDen ν G (Lv.g L) := by rw [hdef]; push_cast; linarith
        exact_mod_cast this
      · intro b _ hb1 _
        rw [hcm]; simp only [GridData.leftEnd, hqL, he, hdt]
        have hb := hb1 hpos
        have : 2 / Lv.den' L + Lv.den L ^ (-γ) < 1 / Lv.den L := by
          have : 3 / 4 / Lv.den L < 1 / Lv.den L := div_lt_div_of_pos_right (by norm_num) hq
          linarith
        push_cast at hb ⊢; rw [add_div] at hb; linarith
      · intro b hb _ _
        rw [hcm1]; simp only [GridData.leftEnd, hqL, he]
        rw [abs_lt] at hb; rw [abs_of_pos hpos] at hb hθb
        have : 1 / Lv.den' L < 2 / Lv.den' L := by
          rw [div_lt_div_iff_of_pos_right hden']; norm_num
        linarith [hb.2]
  obtain ⟨t, ht1, htq, htb⟩ := base_exists (Lv := Lv) P L hg1 hgq
  obtain ⟨hs1, hs2, hs3⟩ := shift_bounds (Lv := Lv) P L ht1 htq
  set b := (gp : ℝ) / Lv.den L + t * Lv.θ L / Lv.den L
  have hbd : |b - gp / Lv.den L| < |Lv.θ L| := by simp only [b, add_sub_cancel_left]; exact hs1
  have hb1 := hbelow b hbd (fun h => by simp only [b]; linarith [hs2 h])
    (fun h => by simp only [b]; linarith [hs3 h])
  have hb2 := habove b hbd (fun h => by simp only [b]; linarith [hs2 h])
    (fun h => by simp only [b]; linarith [hs3 h])
  have hph : ph ν G (t - 1) = b := by
    rw [ph_fract, ← htb]
    congr 2
    rw [Nat.cast_sub ht1]; push_cast; ring
  have hatom : wt ν G (t - 1) ≤ inc ν G u v := atom_le_inc (φ := ph ν G)
    (wt_summable (ν := ν) (G := G)) (wt_nonneg (ν := ν) (G := G)) (k := t - 1)
    (show u < ph ν G (t - 1) by rw [hph]; linarith) (show ph ν G (t - 1) < v by rw [hph]; linarith)
  refine le_trans ?_ hatom
  refine le_trans ?_ (hwA (t - 1))
  apply div_le_div_of_nonneg_left hA.le (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  rw [Nat.cast_sub ht1]; push_cast
  have : (t : ℝ) < Lv.den L := by unfold den; exact_mod_cast htq
  linarith

omit P in
/-- **Chain of a base.** If `{tα} = b` and `b + mθ ∈ [0, 1)`, the phase of index
`mq + t` sits at `b + mθ`. -/
theorem chain_ph (l : ℕ) {t : ℕ} (ht : 1 ≤ t) {b : ℝ}
    (htb : Int.fract ((t : ℝ) * isoSlope ν G) = b) (m : ℕ)
    (h0 : 0 ≤ b + m * Lv.θ l) (h1 : b + m * Lv.θ l < 1) :
    ph ν G (m * isoDen ν G (Lv.g l) + t - 1) = b + m * Lv.θ l := by
  rw [ph_fract]
  have hc : ((m * isoDen ν G (Lv.g l) + t - 1 : ℕ) : ℝ) + 1 = m * Lv.den l + t := by
    rw [Nat.cast_sub (by omega)]; unfold den; push_cast; ring
  rw [hc, Int.fract_eq_iff]
  refine ⟨h0, h1, ⌊(t : ℝ) * isoSlope ν G⌋ + m * cfNum (isoQuot ν G) (Lv.g l), ?_⟩
  have := Int.self_sub_fract ((t : ℝ) * isoSlope ν G)
  rw [htb] at this
  unfold θ; push_cast; linarith

/-- **Chain inside a window.** Let `(u, v)` lie in a charged window of tree level
`j + 1` (good level `j`) with `(v - u) Q'_j ≥ 2`. The chain of the window's base
puts atom mass at least `((v-u) Q'_j / 2) A (4 d_j Q'_j Q_j)^(-3/2)` in it. -/
theorem chain_window (j : ℕ) {a u v : ℝ} (ha : (Lv.grid P).tree.Charged (j + 1) a)
    (hu : a ≤ u) (huv : u < v) (hv : v ≤ a + Lv.den j ^ (-γ))
    (hw : 2 ≤ (v - u) * Lv.den' j) {A : ℝ} (hA : 0 < A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k) :
    (v - u) * Lv.den' j / 2 * (A / (4 * Lv.den j ^ (-γ) * Lv.den' j * Lv.den j) ^ (3/2 : ℝ)) ≤
      inc ν G u v := by
  set D := Lv.grid P
  obtain ⟨i, hi2, hiq, rfl⟩ := D.charged_index ha
  have hqj : (D.q (j + 1) : ℝ) = Lv.den j := rfl
  rw [hqj] at hiq
  have hq := den_pos (Lv := Lv) P j
  have hq' := den'_pos (Lv := Lv) P j
  set d := Lv.den j ^ (-γ) with hd
  have hdp : 0 < d := Real.rpow_pos_of_pos hq _
  have hdq := dq' (Lv := Lv) P j
  obtain ⟨hm1, hm2⟩ := margins (Lv := Lv) P j
  obtain ⟨hθ1, hθ2⟩ := Lv.θ_bounds j
  have hθ := θ_ne (Lv := Lv) j
  have hθa : 0 < |Lv.θ j| := abs_pos.2 hθ
  have hiq' : i < isoDen ν G (Lv.g j) := by
    have : (i : ℝ) < isoDen ν G (Lv.g j) := by
      show (i : ℝ) < Lv.den j; linarith
    exact_mod_cast this
  obtain ⟨t, ht1, htq, htb⟩ := base_exists (Lv := Lv) P j (by omega : 1 ≤ i) hiq'
  obtain ⟨hs1, hs2, hs3⟩ := shift_bounds (Lv := Lv) P j ht1 htq
  set b := (i : ℝ) / Lv.den j + t * Lv.θ j / Lv.den j with hb
  set K := ⌊3 * d * Lv.den' j⌋₊ with hK
  have hK1 : (K : ℝ) ≤ 3 * d * Lv.den' j := Nat.floor_le (by positivity)
  have hK2 : 3 * d * Lv.den' j - 1 < K := by
    have := Nat.lt_floor_add_one (3 * d * Lv.den' j); linarith
  -- the chain stays in `[(i - 1/2)/q, (i + 1/2)/q] ⊂ (0, 1)`
  have hshift : |b - i / Lv.den j| < 1 / Lv.den' j := by
    have : b - i / Lv.den j = t * Lv.θ j / Lv.den j := by simp only [b]; ring
    rw [this]; linarith
  have hmθ : ∀ m : ℕ, m ≤ K → |(m : ℝ) * Lv.θ j| ≤ 3 * d := by
    intro m hm
    have hmR : (m : ℝ) ≤ K := by exact_mod_cast hm
    rw [abs_mul, Nat.abs_cast]
    calc (m : ℝ) * |Lv.θ j| ≤ K * (1 / Lv.den' j) :=
          mul_le_mul hmR hθ2 hθa.le (by positivity)
      _ ≤ 3 * d * Lv.den' j * (1 / Lv.den' j) := by gcongr
      _ = 3 * d := by field_simp
  have hi2R : (2 : ℝ) ≤ i := by exact_mod_cast hi2
  have hlo : 1 / 2 / Lv.den j ≤ (i : ℝ) / Lv.den j - 1 / Lv.den' j - 3 * d := by
    have : (i : ℝ) / Lv.den j ≥ 1 / Lv.den j + 1 / Lv.den j := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    have : 1 / Lv.den j = 1 / 2 / Lv.den j + 1 / 2 / Lv.den j := by ring
    linarith
  have hhi : (i : ℝ) / Lv.den j + 1 / Lv.den' j + 3 * d ≤ 1 - 1 / 2 / Lv.den j := by
    have : (i : ℝ) / Lv.den j + 3 / Lv.den j ≤ 1 := by
      rw [← add_div, div_le_one hq]; linarith
    have : 3 / Lv.den j = 1 / 2 / Lv.den j + 1 / 2 / Lv.den j + 2 / Lv.den j := by ring
    have : 0 < 1 / Lv.den j := by positivity
    have : 0 < 2 / Lv.den j := by positivity
    linarith
  have hhalf : 0 < 1 / 2 / Lv.den j := by positivity
  have hchain : ∀ m, m ≤ K →
      ph ν G (m * isoDen ν G (Lv.g j) + t - 1) = b + m * Lv.θ j := by
    intro m hm
    have h := hmθ m hm
    rw [abs_le] at h
    rw [abs_lt] at hshift
    exact chain_ph (Lv := Lv) j ht1 htb m (by linarith) (by linarith)
  have hKθ : 3 * d / 2 - 1 / (2 * Lv.den' j) ≤ K * |Lv.θ j| := by
    calc 3 * d / 2 - 1 / (2 * Lv.den' j) = (3 * d * Lv.den' j - 1) * (1 / (2 * Lv.den' j)) := by
          field_simp
      _ ≤ K * |Lv.θ j| := mul_le_mul hK2.le hθ1 (by positivity) (by positivity)
  have hroom : 2 / Lv.den' j + d ≤ 3 * d / 2 - 1 / (2 * Lv.den' j) := by
    have : 5 / Lv.den' j ≤ d := by rw [div_le_iff₀ hq']; linarith
    have e1 : 2 / Lv.den' j + 1 / (2 * Lv.den' j) = 5 / Lv.den' j / 2 := by
      field_simp; ring
    linarith
  have h21 : 2 / Lv.den' j = 1 / Lv.den' j + 1 / Lv.den' j := by ring
  have hr1 : 0 < 1 / Lv.den' j := by positivity
  have hbetween : (0 < Lv.θ j ∧ b ≤ u ∧ v ≤ b + K * Lv.θ j) ∨
      (Lv.θ j < 0 ∧ b + K * Lv.θ j ≤ u ∧ v ≤ b) := by
    rw [abs_lt] at hshift
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have hs : Lv.side j = false := by simp [side, not_lt.2 hneg.le]
      have he : D.e (j + 1) = -(2 / Lv.den' j) - d := by
        show (if D.pos (j + 1) then _ else _) = _
        simp only [D, grid, hs]; rfl
      have hleft : D.leftEnd (j + 1) i = i / Lv.den j - 2 / Lv.den' j - d := by
        simp only [GridData.leftEnd, hqj, he]; ring
      have hdj : D.d (j + 1) = d := rfl
      rw [abs_of_neg hneg] at hKθ
      have hKθ' : (K : ℝ) * Lv.θ j = -(K * -Lv.θ j) := by ring
      have hb3 := hs3 hneg
      have hbi : b ≤ i / Lv.den j := by simp only [b]; linarith
      refine Or.inr ⟨hneg, ?_, ?_⟩
      · rw [hleft] at hu; linarith [hshift.1, hshift.2]
      · rw [hleft] at hv; linarith [hshift.1, hshift.2]
    · have hs : Lv.side j = true := by simp [side, hpos]
      have he : D.e (j + 1) = 2 / Lv.den' j := by
        show (if D.pos (j + 1) then _ else _) = _
        simp only [D, grid, hs, if_true]
      have hleft : D.leftEnd (j + 1) i = i / Lv.den j + 2 / Lv.den' j := by
        simp only [GridData.leftEnd, hqj, he]
      rw [abs_of_pos hpos] at hKθ
      have hb3 := hs2 hpos
      have hbi : i / Lv.den j ≤ b := by simp only [b]; linarith
      refine Or.inl ⟨hpos, ?_, ?_⟩
      · rw [hleft] at hu; linarith [hshift.1, hshift.2]
      · rw [hleft] at hv; linarith [hshift.1, hshift.2]
  have hmain := chain_le_inc (φ := ph ν G) (w := wt ν G)
    (wt_summable (ν := ν) (G := G)) (wt_nonneg (ν := ν) (G := G)) hA.le hwA
    (q := isoDen ν G (Lv.g j)) (K := K) ht1 hθ hchain huv hbetween
  refine le_trans ?_ hmain
  have hqq : ((isoDen ν G (Lv.g j) : ℕ) : ℝ) = Lv.den j := rfl
  rw [hqq]
  apply mul_le_mul _ _ (by positivity) _
  · -- the count
    have : (v - u) * Lv.den' j ≤ (v - u) / |Lv.θ j| := by
      rw [le_div_iff₀ hθa]
      calc (v - u) * Lv.den' j * |Lv.θ j| ≤ (v - u) * Lv.den' j * (1 / Lv.den' j) := by
            gcongr
        _ = v - u := by field_simp
    linarith
  · -- the index
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have htR : (t : ℝ) ≤ Lv.den j := by
      have : (t : ℝ) < isoDen ν G (Lv.g j) := by exact_mod_cast htq
      exact this.le
    have h1 : 1 ≤ d * Lv.den' j := by linarith
    nlinarith
  · have : 0 ≤ (v - u) / |Lv.θ j| - 1 := by
      have : (v - u) * Lv.den' j ≤ (v - u) / |Lv.θ j| := by
        rw [le_div_iff₀ hθa]
        calc (v - u) * Lv.den' j * |Lv.θ j| ≤ (v - u) * Lv.den' j * (1 / Lv.den' j) := by
              gcongr
          _ = v - u := by field_simp
      linarith
    exact this

omit P in
/-- A denominator at most `20/ℓ` gives weight at least `A ℓ^(3/2) / 20^(3/2)`. -/
theorem weight_of_den_le {A ℓ Q : ℝ} (hA : 0 ≤ A) (hℓ : 0 < ℓ) (hQ : 0 < Q)
    (hQℓ : Q * ℓ ≤ 20) :
    A * ℓ ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ) ≤ A / Q ^ (3/2 : ℝ) := by
  have hQ' : Q ≤ 20 / ℓ := by rw [le_div_iff₀ hℓ]; exact hQℓ
  have h1 : Q ^ (3/2 : ℝ) ≤ (20 / ℓ) ^ (3/2 : ℝ) :=
    Real.rpow_le_rpow hQ.le hQ' (by norm_num)
  have h2 : (20 / ℓ) ^ (3/2 : ℝ) = 20 ^ (3/2 : ℝ) / ℓ ^ (3/2 : ℝ) :=
    Real.div_rpow (by norm_num) hℓ.le _
  have hp : 0 < ℓ ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have hp2 : (0 : ℝ) < 20 ^ (3/2 : ℝ) := by positivity
  calc A * ℓ ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ) = A / (20 / ℓ) ^ (3/2 : ℝ) := by
        rw [h2]; field_simp
    _ ≤ A / Q ^ (3/2 : ℝ) :=
        div_le_div_of_nonneg_left hA (Real.rpow_pos_of_pos hQ _) h1

omit P in
/-- **Many hits at intermediate scales.** If `20/Q_(g(j+1)) ≤ v - u ≤ 10/Q_(g j + 1)`,
some convergent denominator lies in `[10/ℓ, 20/ℓ]`, and its rotation hits
give atom mass at least `A ℓ^(3/2) / 20^(3/2)`. -/
theorem hits_scale (j : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (h1 : 20 ≤ (v - u) * Lv.den (j + 1)) (h2 : (v - u) * Lv.den' j ≤ 10) {A : ℝ} (hA : 0 ≤ A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k) :
    A * (v - u) ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ) ≤ inc ν G u v := by
  classical
  have hℓ : 0 < v - u := by linarith
  have hex : ∃ k, Lv.g j + 1 ≤ k ∧ 10 ≤ (v - u) * isoDen ν G k :=
    ⟨Lv.g (j + 1), Lv.mono (Nat.lt_succ_self j), by unfold den at h1; linarith⟩
  obtain ⟨k, ⟨hk1, hk2⟩, hkmin⟩ : ∃ k, (Lv.g j + 1 ≤ k ∧ 10 ≤ (v - u) * isoDen ν G k) ∧
      ∀ k' < k, ¬ (Lv.g j + 1 ≤ k' ∧ 10 ≤ (v - u) * isoDen ν G k') :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ h => Nat.find_min hex h⟩
  have hkle : k ≤ Lv.g (j + 1) := by
    by_contra hc
    exact hkmin _ (not_le.1 hc) ⟨Lv.mono (Nat.lt_succ_self j), by unfold den at h1; linarith⟩
  have hk0 : 1 ≤ k := by omega
  have hQ : 0 < isoDen ν G k := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact isoDen_pos n
  have hQR : (0 : ℝ) < isoDen ν G k := by exact_mod_cast hQ
  have hupper : (isoDen ν G k : ℝ) * (v - u) ≤ 20 := by
    rcases Nat.eq_or_lt_of_le hk1 with he | hlt
    · subst he; unfold den' at h2; linarith
    · have hmin := hkmin (k - 1) (by omega)
      have hk' : Lv.g j + 1 ≤ k - 1 := by omega
      have hlow : (v - u) * isoDen ν G (k - 1) < 10 := by
        by_contra hc; exact hmin ⟨hk', not_lt.1 hc⟩
      have hng : ¬ G (k - 1) := Lv.not_good (l := j) (by omega) (by omega)
      have := isoDen_succ_le_two (ν := ν) (show 1 ≤ k - 1 by omega) hng
      rw [show k - 1 + 1 = k by omega] at this
      nlinarith
  have hmain := hits_le_inc (φ := ph ν G) (w := wt ν G) (α := isoSlope ν G)
    (wt_summable (ν := ν) (G := G)) (wt_nonneg (ν := ν) (G := G)) hA hwA
    (fun n => ph_fract n) hQ (iso_coprime k hk0) (iso_approx k hk0) hu huv hv
    (by linarith)
  refine le_trans ?_ hmain
  have hc1 : 1 ≤ (isoDen ν G k : ℝ) * (v - u) / 10 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have hw := weight_of_den_le hA hℓ hQR hupper
  have hpos : 0 ≤ A / (isoDen ν G k : ℝ) ^ (3/2 : ℝ) := by positivity
  nlinarith

omit P in
/-- The atom mass of an interval is nonnegative. -/
theorem inc_nonneg {u v : ℝ} (huv : u < v) : 0 ≤ inc ν G u v :=
  sub_nonneg.2 (jumpProfileRight_le_of_lt wt_summable (wt_nonneg (ν := ν) (G := G)) huv)

omit P in
/-- The atom mass does not increase when the interval shrinks. -/
theorem inc_mono {u v u' v' : ℝ} (hu : u ≤ u') (_huv : u' < v') (hv : v' ≤ v) :
    inc ν G u' v' ≤ inc ν G u v := by
  unfold inc
  have hw := wt_summable (ν := ν) (G := G)
  have hn := wt_nonneg (ν := ν) (G := G)
  have h1 : jumpProfile (ph ν G) (wt ν G) v' ≤ jumpProfile (ph ν G) (wt ν G) v :=
    jumpProfile_monotone hw hn hv
  have h2 : jumpProfileRight (ph ν G) (wt ν G) u ≤ jumpProfileRight (ph ν G) (wt ν G) u' := by
    rcases eq_or_lt_of_le hu with h | h
    · rw [h]
    · exact (jumpProfileRight_le_of_lt hw hn h).trans (jumpProfile_le_right hw hn u')
  linarith

/-- **Small scales.** An interval inside a charged window of tree level `j + 1`,
meeting two of its children, with `(v - u) Q'_j ≤ 10`, has atom mass at least
`A ℓ^(3/2) / 20^(3/2)`. -/
theorem small_scale (j : ℕ) {a u v : ℝ} (ha : (Lv.grid P).tree.Charged (j + 1) a) {m m' : ℕ}
    (hmm : m < m') (hm' : m' < (Lv.grid P).tree.N (j + 1))
    (h1 : u < (Lv.grid P).tree.child (j + 1) a m + (Lv.grid P).tree.d (j + 2))
    (h2 : (Lv.grid P).tree.child (j + 1) a m' < v) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hsmall : (v - u) * Lv.den' j ≤ 10) {A : ℝ} (hA : 0 < A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ wt ν G k) :
    A * (v - u) ^ (3/2 : ℝ) / 20 ^ (3/2 : ℝ) ≤ inc ν G u v := by
  by_cases hc : (v - u) * Lv.den (j + 1) ≤ 20
  · refine le_trans ?_ (base_between (Lv := Lv) P (j + 1) ha hmm hm' h1 h2 hA hwA)
    exact weight_of_den_le hA.le (by linarith) (den_pos (Lv := Lv) P _) (by linarith)
  · exact hits_scale (Lv := Lv) j hu huv hv (by linarith) hsmall hA.le hwA

end IsoLevels

end Problems.Juggler.BeattySlope
