import Problems.Juggler.BeattyTwoScale

/-!
# Two-scale slopes: the upper bound

Let `p/q` be good convergents of `α` and `n₀ < n₁ < …` the jump indices, with
`q(n_j)^ν ≤ q(n_j + 1)` and `q(n_(j+1)) ≤ q(n_j + 1)^ρ'` from some level on. Cells of
level `q` are phase intervals of length at most `4/q` holding no phase of index
below `q`. A level-`q(n_j)` cell is refined in two moves:

* **chain step** (`cell_refine_step`) at `q = q(n_j)`, `q' = q(n_j + 1)`;
* **pass-through** (`cell_pass_step`): a level-`q(n_j + 1)` cell is cut at the phases of
  index below `q(n_(j+1))`, and every piece is a cell of the next jump level.

In exponents the cover cost `q^(-σ)` improves by a fixed `δ > 0` at every jump
level while `3s/2 ≤ σ ≤ 1`, provided `s > 2/(2+ν)` and
`3(νρ'-1)s² + 4(ρ'-1)s - 4(ρ'-1) > 0`. Finitely many steps reach `σ > 1`, so
`H^s(K_α) = 0`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase

/-- **Pass-through.** A phase interval of length at most `4/N` is covered by
cells of level `q''` at cost `(9(q''/N + 1) + 2) X`, when `N` separates the orbit
and `p''/q''` is a reduced approximation with `|α - p''/q''| ≤ q''^(-2)`. -/
theorem cell_pass_step {φ w : ℕ → ℝ} {α : ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {s : ℝ}
    {N q'' : ℕ} {p'' : ℤ} (hN : 0 < N) (hq'' : 0 < q'')
    (hcop'' : Nat.Coprime p''.natAbs q'') (happ'' : |α - p'' / q''| ≤ 1 / (q'' : ℝ) ^ 2)
    (hsep : ∀ m : ℕ, 0 < m → m < N → ∀ r : ℤ, 1 / (2 * (N : ℝ)) ≤ |(m : ℝ) * α - r|)
    {X : ℝ}
    (hX : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → d - c ≤ 4 / q'' →
      (∀ k < q'', φ k ∉ Ioo c d) → CellCover φ w s c d X) (hX0 : 0 ≤ X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hlen : b - a ≤ 4 / N) :
    CellCover φ w s a b ((9 * ((q'' : ℝ) / N + 1) + 2) * X) := by
  classical
  have hcount := cell_block_count hfr hN hsep hab.le hlen
  set Cut := ((Finset.range q'').filter (fun k => φ k ∈ Ioo a b)).image φ
  set C' : Finset ℝ := insert a (insert b Cut)
  have haC : a ∈ C' := Finset.mem_insert_self _ _
  have hbC : b ∈ C' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hCut : ∀ e ∈ Cut, ∃ k < q'', φ k ∈ Ioo a b ∧ φ k = e := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    exact ⟨k, Finset.mem_range.1 hk1, hk2, rfl⟩
  have hCab : ∀ e ∈ C', a ≤ e ∧ e ≤ b := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨le_rfl, hab.le⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨hab.le, le_rfl⟩
    obtain ⟨k, -, hk, rfl⟩ := hCut e he
    exact ⟨hk.1.le, hk.2.le⟩
  have hno : ∀ g ∈ cutGaps C', ∀ k < q'', φ k ∉ Ioo g.1 g.2 := by
    intro g hg k hk hmem
    obtain ⟨c1, c2, -, hsepg⟩ := mem_cutGaps.1 hg
    have hin : φ k ∈ Ioo a b := ⟨(hCab _ c1).1.trans_lt hmem.1, hmem.2.trans_le (hCab _ c2).2⟩
    have hkC : φ k ∈ C' := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hin⟩, rfl⟩))
    rcases hsepg _ hkC with h | h
    · linarith [hmem.1]
    · linarith [hmem.2]
  have hcov := cellCover_of_gaps (φ := φ) (w := w) (s := s) hw hn haC hbC (fun _ => X) (by
    intro g hg
    obtain ⟨c1, c2, hlt, -⟩ := mem_cutGaps.1 hg
    exact hX g.1 g.2 (ha.trans (hCab _ c1).1) hlt ((hCab _ c2).2.trans hb1)
      (gap_short_of_approx hfr hq'' hcop'' happ'' (ha.trans (hCab _ c1).1)
        ((hCab _ c2).2.trans hb1) fun k hk => hno g hg k (by omega))
      (hno g hg))
  refine hcov.mono ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcutc : (Cut.card : ℝ) ≤ 9 * ((q'' : ℝ) / N + 1) :=
    (Nat.cast_le.2 Finset.card_image_le).trans (card_range_filter_le hN hcount q'')
  have hgc : ((cutGaps C').card : ℝ) ≤ 9 * ((q'' : ℝ) / N + 1) + 2 := by
    have h1 : (cutGaps C').card ≤ C'.card := card_cutGaps_le C'
    have h2 : C'.card ≤ Cut.card + 2 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
    have h3 : ((cutGaps C').card : ℝ) ≤ Cut.card + 2 := by exact_mod_cast h1.trans h2
    linarith
  exact mul_le_mul_of_nonneg_right hgc hX0

/-- **Uniform gain.** For `ν ≥ 1`, `ρ ≥ 1`, `2/(2+ν) < s < 2/3` and
`3(νρ-1)s² + 4(ρ-1)s - 4(ρ-1) > 0`, some `δ > 0` works at every `σ ∈ [3s/2, 1]`:
with `σ_N = max(3s/2, 1 + ρ(σ-1))` there is `y ∈ [1, ν]` with
`σ + δ ≤ s(1 + y/2)` and `σ + δ ≤ ν σ_N + 1 - y`. -/
theorem twoScale_gain {ν ρ s : ℝ} (hν : 1 ≤ ν) (hρ : 1 ≤ ρ) (hs : 2 / (2 + ν) < s)
    (hs23 : s < 2 / 3)
    (hQ : 0 < 3 * (ν * ρ - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 3 * s / 2 ≤ σ → σ ≤ 1 →
      ∃ y : ℝ, 1 ≤ y ∧ y ≤ ν ∧ σ + δ ≤ s * (1 + y / 2) ∧
        σ + δ ≤ ν * max (3 * s / 2) (1 + ρ * (σ - 1)) + 1 - y := by
  have hs0 : 0 < s := lt_trans (by positivity) hs
  have hsν : 2 < s * (2 + ν) := by rwa [div_lt_iff₀ (by positivity)] at hs
  set f := 3 * s / 2 - 1 with hf
  have hf0 : f < 0 := by rw [hf]; linarith
  -- `E(u) = (s(1+ν/2) - 1 + (sν/2) u)/(1 + s/2)` is the equalized value minus one
  set e1 := s * ν / 2 / (1 + s / 2) with he1
  have he1p : 0 ≤ e1 := by positivity
  set E0 := (s * (2 + ν) - 2) / (s + 2) with hE0
  have hE0p : 0 < E0 := by rw [hE0]; apply div_pos (by linarith) (by positivity)
  set Ef := E0 + e1 * f with hEf
  -- `ρ E(f) - f = Q/(2(2+s))`
  have hgap : ρ * Ef - f = (3 * (ν * ρ - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) /
      (2 * (2 + s)) := by
    rw [hEf, hE0, he1, hf]; field_simp; ring
  set g1 := (ρ * Ef - f) / ρ with hg1
  have hρ0 : 0 < ρ := by linarith
  have hg1p : 0 < g1 := by
    rw [hg1, hgap]; positivity
  refine ⟨min g1 E0, lt_min hg1p hE0p, fun σ hσ1 hσ2 => ?_⟩
  set σN := max (3 * s / 2) (1 + ρ * (σ - 1)) with hσN
  have hσN1 : 3 * s / 2 ≤ σN := le_max_left _ _
  have hσN2 : σN ≤ 1 := max_le (by linarith) (by nlinarith)
  set y := (ν * σN - s + 1) / (1 + s / 2) with hy
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]; nlinarith
  have hyν : y ≤ ν := by
    rw [hy, div_le_iff₀ (by positivity)]; nlinarith
  -- the two constraints are equal at this `y`
  have heq : s * (1 + y / 2) = ν * σN + 1 - y := by
    rw [hy]; field_simp; ring
  -- `s(1 + y/2) - 1 = E0 + e1 (σN - 1)`
  have hval : s * (1 + y / 2) - 1 = E0 + e1 * (σN - 1) := by
    rw [hy, hE0, he1]; field_simp; ring
  have hgain : σ + min g1 E0 ≤ s * (1 + y / 2) := by
    rw [show s * (1 + y / 2) = 1 + (E0 + e1 * (σN - 1)) by linarith]
    by_cases hcase : 1 + ρ * (σ - 1) ≤ 3 * s / 2
    · -- floor branch: `σN - 1 = f` and `σ - 1 ≤ f/ρ`
      have hN : σN - 1 = f := by
        rw [hσN, max_eq_left hcase, hf]
      rw [hN]
      have hw : σ - 1 ≤ f / ρ := by rw [le_div_iff₀ hρ0, hf]; linarith
      have : g1 = Ef - f / ρ := by rw [hg1]; field_simp
      have := min_le_left g1 E0
      rw [hEf] at *
      linarith
    · -- pass branch: `σN - 1 = ρ(σ-1)`, affine in `σ - 1 ∈ [f/ρ, 0]`
      push Not at hcase
      have hN : σN - 1 = ρ * (σ - 1) := by
        rw [hσN, max_eq_right hcase.le]; ring
      rw [hN]
      have hw0 : σ - 1 ≤ 0 := by linarith
      have hwf : f / ρ ≤ σ - 1 := by rw [div_le_iff₀ hρ0, hf]; linarith
      have hg1' : g1 = E0 + e1 * f - f / ρ := by rw [hg1, hEf]; field_simp
      by_cases hk : 0 ≤ e1 * ρ - 1
      · -- nondecreasing: the minimum is at `σ - 1 = f/ρ`
        have h1 : E0 + e1 * f - f / ρ ≤ E0 + e1 * (ρ * (σ - 1)) - (σ - 1) := by
          have hfr : e1 * f = (e1 * ρ) * (f / ρ) := by field_simp
          rw [hfr]
          nlinarith
        have := min_le_left g1 E0
        linarith
      · push Not at hk
        -- nonincreasing: the minimum is at `σ - 1 = 0`
        have h1 : E0 ≤ E0 + e1 * (ρ * (σ - 1)) - (σ - 1) := by nlinarith
        have := min_le_right g1 E0
        linarith
  exact ⟨y, hy1, hyν, hgain, heq ▸ hgain⟩

/-- Pass-through in exponents: for `1 ≤ Q' ≤ Q'' ≤ Q'^ρ` and `σ ≤ 1`,
`(9(Q''/Q' + 1) + 2) K Q''^(-σ) ≤ 20 K Q'^(-(1 + ρ(σ-1)))`. -/
theorem pass_cost_le {Q' Q'' K ρ σ : ℝ} (hQ' : 1 ≤ Q') (hQQ : Q' ≤ Q'') (hup : Q'' ≤ Q' ^ ρ)
    (hσ : σ ≤ 1) (hK : 0 ≤ K) :
    (9 * (Q'' / Q' + 1) + 2) * (K * Q'' ^ (-σ)) ≤ 20 * K * Q' ^ (-(1 + ρ * (σ - 1))) := by
  have hQ'0 : 0 < Q' := by linarith
  have hQ''0 : 0 < Q'' := by linarith
  have hx : 1 ≤ Q'' / Q' := by rw [le_div_iff₀ hQ'0]; linarith
  have h1 : 9 * (Q'' / Q' + 1) + 2 ≤ 20 * (Q'' / Q') := by linarith
  have h2 : Q'' / Q' * Q'' ^ (-σ) = Q'' ^ (1 - σ) / Q' := by
    rw [show (1 - σ) = 1 + -σ by ring, Real.rpow_add hQ''0, Real.rpow_one]; ring
  have h3 : Q'' ^ (1 - σ) ≤ (Q' ^ ρ) ^ (1 - σ) :=
    Real.rpow_le_rpow hQ''0.le hup (by linarith)
  have h4 : (Q' ^ ρ) ^ (1 - σ) / Q' = Q' ^ (-(1 + ρ * (σ - 1))) := by
    rw [← Real.rpow_mul hQ'0.le, div_eq_mul_inv, ← Real.rpow_neg_one,
      ← Real.rpow_add hQ'0]
    congr 1; ring
  have hpos : 0 ≤ K * Q'' ^ (-σ) := by positivity
  calc (9 * (Q'' / Q' + 1) + 2) * (K * Q'' ^ (-σ))
      ≤ 20 * (Q'' / Q') * (K * Q'' ^ (-σ)) := mul_le_mul_of_nonneg_right h1 hpos
    _ = 20 * K * (Q'' / Q' * Q'' ^ (-σ)) := by ring
    _ = 20 * K * (Q'' ^ (1 - σ) / Q') := by rw [h2]
    _ ≤ 20 * K * ((Q' ^ ρ) ^ (1 - σ) / Q') := by
        gcongr
    _ = 20 * K * Q' ^ (-(1 + ρ * (σ - 1))) := by rw [h4]

/-- Covers of the cells at the jump levels `q (n j)`, `j ≥ j₁`, at cost `K q^(-σ)`. -/
def JumpCovers (φ w : ℕ → ℝ) (q n : ℕ → ℕ) (s σ K : ℝ) (j₁ : ℕ) : Prop :=
  ∀ j, j₁ ≤ j → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → b - a ≤ 4 / q (n j) →
    (∀ k < q (n j), φ k ∉ Ioo a b) → CellCover φ w s a b (K * (q (n j) : ℝ) ^ (-σ))

/-- **One jump level.** Covers at the next jump level with exponent `σ ∈ [3s/2, 1]`
give covers at this level with any `σ' ≤ s(1+y/2)` and
`σ' ≤ ν max(3s/2, 1 + ρ(σ-1)) + 1 - y`, `1 ≤ y ≤ ν`. -/
theorem jumpCovers_step {φ w : ℕ → ℝ} {α ν ρ : ℝ} (hα : Irrational α) (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ} (hs : 0 < s)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hmono : Monotone q)
    {n : ℕ → ℕ} (hnm : StrictMono n) (_hν : 1 ≤ ν) (_hρ : 1 ≤ ρ) {j₀ : ℕ}
    (hgrow : ∀ j, j₀ ≤ j → (q (n j) : ℝ) ^ ν ≤ q (n j + 1))
    (hup : ∀ j, j₀ ≤ j → (q (n (j + 1)) : ℝ) ≤ (q (n j + 1) : ℝ) ^ ρ)
    {σ K : ℝ} {j₁ : ℕ} (hσ1 : 3 * s / 2 ≤ σ) (hσ2 : σ ≤ 1) (hK : 0 ≤ K)
    (hL : JumpCovers φ w q n s σ K j₁)
    {y σ' : ℝ} (hy1 : 1 ≤ y) (hyν : y ≤ ν) (h1 : σ' ≤ s * (1 + y / 2))
    (h2 : σ' ≤ ν * max (3 * s / 2) (1 + ρ * (σ - 1)) + 1 - y) :
    JumpCovers φ w q n s σ' (7 * (54 * B) ^ s + 20 * ((27 * B) ^ s + 20 * K)) (max j₁ j₀) := by
  intro j hj a b ha hab hb1 hlen hno
  have hB := weight_const_nonneg hn hb
  have hj1 : j₁ ≤ j := le_of_max_le_left hj
  have hj0 : j₀ ≤ j := le_of_max_le_right hj
  set Q := q (n j) with hQdef
  set Q' := q (n j + 1) with hQ'def
  set Q'' := q (n (j + 1)) with hQ''def
  have hq := hG.pos (n j)
  have hq' := hG.pos (n j + 1)
  have hq'' := hG.pos (n (j + 1))
  have hqR : (1 : ℝ) ≤ Q := by exact_mod_cast hq
  have hq'R : (1 : ℝ) ≤ Q' := by exact_mod_cast hq'
  have hQ'Q'' : (Q' : ℝ) ≤ Q'' := by
    have : n j + 1 ≤ n (j + 1) := hnm (Nat.lt_succ_self j)
    exact_mod_cast hmono this
  set σN := max (3 * s / 2) (1 + ρ * (σ - 1)) with hσN
  have hσN0 : 0 ≤ σN := le_trans (by positivity) (le_max_left _ _)
  set KN := (27 * B) ^ s + 20 * K with hKN
  have hKN0 : 0 ≤ KN := by positivity
  -- covers of the level-`Q'` cells
  have hXN : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → d - c ≤ 4 / Q' →
      (∀ k < Q', φ k ∉ Ioo c d) → CellCover φ w s c d (KN * (Q' : ℝ) ^ (-σN)) := by
    intro c d hc hcd hd hl hno'
    by_cases hcase : 1 + ρ * (σ - 1) ≤ 3 * s / 2
    · have hσNe : σN = 3 * s / 2 := max_eq_left hcase
      have hself := levelCovers_base hw hn hfr hb hs hG (n j + 1) (Nat.zero_le _) c d hc hcd hd
        hl hno'
      refine hself.mono ?_
      rw [hσNe]
      have : (27 * B) ^ s ≤ KN := by rw [hKN]; linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 20) hK]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · push Not at hcase
      have hσNe : σN = 1 + ρ * (σ - 1) := max_eq_right hcase.le
      have hmono'' : q (n (j + 1)) ≤ q (n (j + 1) + 1) := hmono (Nat.le_succ _)
      have hpass := cell_pass_step (φ := φ) (w := w) (s := s) hw hn hfr hq' hq''
        (hG.coprime (n (j + 1))) (good_approx_sq hG hmono'') (hG.sep (n j + 1))
        (X := K * (Q'' : ℝ) ^ (-σ))
        (fun c' d' hc' hcd' hd' hl' hno'' =>
          hL (j + 1) (by omega) c' d' hc' hcd' hd' hl' hno'')
        (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) hc hcd hd hl
      refine hpass.mono ?_
      rw [hσNe]
      calc (9 * ((Q'' : ℝ) / Q' + 1) + 2) * (K * (Q'' : ℝ) ^ (-σ))
          ≤ 20 * K * (Q' : ℝ) ^ (-(1 + ρ * (σ - 1))) :=
            pass_cost_le hq'R hQ'Q'' (hup j hj0) hσ2 hK
        _ ≤ KN * (Q' : ℝ) ^ (-(1 + ρ * (σ - 1))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hKN]; linarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 27 * B) s]
  -- the chain step at level `Q`
  have hg0 := hgrow j hj0
  have hmono1 : q (n j + 1) ≤ q (n j + 1 + 1) := hmono (Nat.le_succ _)
  set E := ⌊(Q : ℝ) ^ y⌋₊
  have hQy1 : 1 ≤ (Q : ℝ) ^ y := Real.one_le_rpow hqR (by linarith)
  have hE2 : (E : ℝ) ≤ (Q : ℝ) ^ y := Nat.floor_le (by linarith)
  have hE1 : (Q : ℝ) ^ y / 2 ≤ E := by
    have h1' := Nat.lt_floor_add_one ((Q : ℝ) ^ y)
    have h2' : (1 : ℝ) ≤ E := by exact_mod_cast Nat.le_floor (by simpa using hQy1)
    linarith
  have hqE : Q ≤ E := by
    apply Nat.le_floor
    simpa using Real.rpow_le_rpow_of_exponent_le hqR hy1
  have hEq' : E ≤ Q' := by
    have : (E : ℝ) ≤ Q' :=
      hE2.trans ((Real.rpow_le_rpow_of_exponent_le hqR hyν).trans hg0)
    exact_mod_cast this
  have hstep := cell_refine_step hα hw hn hi hfr hb hs hq hq' (hG.coprime (n j + 1))
    (good_approx_sq hG hmono1) (hG.approx (n j)) (hG.sep (n j)) hqE hEq'
    (X := KN * (Q' : ℝ) ^ (-σN)) hXN
    (mul_nonneg hKN0 (Real.rpow_nonneg (by positivity) _)) ha hab hb1 hlen
  exact hstep.mono (step_cost_le hqR hE1 hE2 hg0 hy1 hσN0 hKN0 hB hs h1 h2)

/-- **Enough jump levels.** Under the gain conditions, jump covers with exponent above
one exist. -/
theorem jumpCovers_exists {φ w : ℕ → ℝ} {α ν ρ : ℝ} (hα : Irrational α) (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ}
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hmono : Monotone q)
    {n : ℕ → ℕ} (hnm : StrictMono n) (hν : 1 ≤ ν) (hρ : 1 ≤ ρ) {j₀ : ℕ}
    (hgrow : ∀ j, j₀ ≤ j → (q (n j) : ℝ) ^ ν ≤ q (n j + 1))
    (hup : ∀ j, j₀ ≤ j → (q (n (j + 1)) : ℝ) ≤ (q (n j + 1) : ℝ) ^ ρ)
    (hs : 2 / (2 + ν) < s) (hs23 : s < 2 / 3)
    (hQ : 0 < 3 * (ν * ρ - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) :
    ∃ σ K j₁, 1 < σ ∧ 0 ≤ K ∧ JumpCovers φ w q n s σ K j₁ := by
  have hB := weight_const_nonneg hn hb
  have hs0 : 0 < s := lt_trans (by positivity) hs
  obtain ⟨δ, hδ, hgain⟩ := twoScale_gain hν hρ hs hs23 hQ
  have hbase : JumpCovers φ w q n s (3 * s / 2) ((27 * B) ^ s) 0 :=
    fun j _ a b ha hab hb1 hlen hno =>
      levelCovers_base hw hn hfr hb hs0 hG (n j) (Nat.zero_le _) a b ha hab hb1 hlen hno
  -- by induction: while `3s/2 + m δ ≤ 1 + δ`, covers at exponent `3s/2 + m δ` exist
  have hind : ∀ m : ℕ, 3 * s / 2 + m * δ ≤ 1 + δ →
      ∃ K j₁, 0 ≤ K ∧ JumpCovers φ w q n s (3 * s / 2 + m * δ) K j₁ := by
    intro m
    induction m with
    | zero => intro _; exact ⟨(27 * B) ^ s, 0, Real.rpow_nonneg (by positivity) _, by simpa using hbase⟩
    | succ m ih =>
      intro hm
      push_cast at hm
      have hσ2 : 3 * s / 2 + m * δ ≤ 1 := by linarith
      obtain ⟨K, j₁, hK, hL⟩ := ih (by linarith)
      have hσ1 : 3 * s / 2 ≤ 3 * s / 2 + m * δ := by
        have : (0 : ℝ) ≤ m * δ := by positivity
        linarith
      obtain ⟨y, hy1, hyν, g1, g2⟩ := hgain _ hσ1 hσ2
      refine ⟨7 * (54 * B) ^ s + 20 * ((27 * B) ^ s + 20 * K), max j₁ j₀,
        by positivity, ?_⟩
      have := jumpCovers_step hα hw hn hi hfr hb hs0 hG hmono hnm hν hρ hgrow hup hσ1 hσ2 hK hL
        hy1 hyν (σ' := 3 * s / 2 + ((m + 1 : ℕ) : ℝ) * δ) (by push_cast; linarith)
        (by push_cast; linarith)
      exact this
  set m := ⌊(1 - 3 * s / 2) / δ⌋₊ + 1 with hm
  have hm1 : 1 < 3 * s / 2 + m * δ := by
    have := Nat.lt_floor_add_one ((1 - 3 * s / 2) / δ)
    rw [hm]; push_cast
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hm2 : 3 * s / 2 + m * δ ≤ 1 + δ := by
    have h0 : 0 ≤ (1 - 3 * s / 2) / δ := div_nonneg (by linarith) hδ.le
    have := Nat.floor_le h0
    rw [hm]; push_cast
    rw [le_div_iff₀ hδ] at this
    nlinarith
  obtain ⟨K, j₁, hK, hL⟩ := hind m hm2
  exact ⟨_, K, j₁, hm1, hK, hL⟩

/-- **Two-scale upper bound.** Let `p/q` be good convergents of an irrational `α > 1`,
with `q` monotone and tending to infinity, and `n` strictly increasing jump indices with
`q(n_j)^ν ≤ q(n_j+1)` and `q(n_(j+1)) ≤ q(n_j+1)^ρ` from some level on. If
`2/(2+ν) < s < 2/3` and `3(νρ-1)s² + 4(ρ-1)s - 4(ρ-1) > 0`, then
`H^s(K_α) = 0`. -/
theorem twoScale_hausdorff_zero {α ν ρ : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hmono : Monotone q)
    (hq : Tendsto q atTop atTop)
    {n : ℕ → ℕ} (hnm : StrictMono n) (hν : 1 ≤ ν) (hρ : 1 ≤ ρ)
    (hgrow : ∀ᶠ j in atTop, (q (n j) : ℝ) ^ ν ≤ q (n j + 1))
    (hup : ∀ᶠ j in atTop, (q (n (j + 1)) : ℝ) ≤ (q (n j + 1) : ℝ) ^ ρ)
    {s : ℝ} (hs : 2 / (2 + ν) < s) (hs23 : s < 2 / 3)
    (hQ : 0 < 3 * (ν * ρ - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) :
    Measure.hausdorffMeasure s (passageClusterSet (1/α)) = 0 := by
  classical
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have hs0 : 0 < s := lt_trans (by positivity) hs
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  set φ : ℕ → ℝ := fun r => passagePhase (1/α) (r+1) with hφdef
  set w : ℕ → ℝ := fun r => passageJumpWeight (1/α) (r+1) with hwdef
  have hw : Summable w := (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  have hn : ∀ n, 0 ≤ w n := fun n => passageJumpWeight_nonneg hβ0 hβ1 _
  have hi : Function.Injective φ :=
    (passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)
  have hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨passagePhase_pos hβ0 hβ1 hβ (Nat.succ_pos n), (passagePhase_mem_Ico hβ0 _).2⟩
  have hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α) := by
    intro k
    simp only [hφdef]
    rw [passagePhase_eq_fract hβ0]
    push_cast
    congr 1
    field_simp
  obtain ⟨A, B, hA, hB, hwB⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  have hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ) := fun n => (hwB n).2
  obtain ⟨j₀a, hga⟩ := eventually_atTop.1 hgrow
  obtain ⟨j₀b, hgb⟩ := eventually_atTop.1 hup
  obtain ⟨σ, K, j₁, hσ1, hK, hL⟩ := jumpCovers_exists hα hw hn hi hfr hb hG hmono hnm hν hρ
    (j₀ := max j₀a j₀b) (fun j hj => hga j (le_of_max_le_left hj))
    (fun j hj => hgb j (le_of_max_le_right hj)) hs hs23 hQ
  apply cellCover_hausdorff_zero hw hn hi hp hs0
  intro ε hε
  have hqn : Tendsto (fun j => q (n j)) atTop atTop := hq.comp hnm.tendsto_atTop
  have tq : Tendsto (fun j => ((q (n j) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqn
  have hlim : Tendsto (fun j => 3 * K * ((q (n j) : ℕ) : ℝ) ^ (-(σ - 1))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).comp tq).const_mul (3 * K)
  obtain ⟨j, hsmall, hj1⟩ := ((hlim.eventually (ge_mem_nhds hε)).and
    (eventually_ge_atTop j₁)).exists
  have hq0 := hG.pos (n j)
  have hqR : (1 : ℝ) ≤ q (n j) := by exact_mod_cast hq0
  set C := earlyCuts φ (q (n j))
  have h0 : (0 : ℝ) ∈ C := mem_earlyCuts.2 (Or.inl rfl)
  have h1 : (1 : ℝ) ∈ C := mem_earlyCuts.2 (Or.inr (Or.inl rfl))
  have hC01 : ∀ e ∈ C, 0 ≤ e ∧ e ≤ 1 := by
    intro e he
    rcases mem_earlyCuts.1 he with rfl | rfl | ⟨k, -, rfl⟩
    · norm_num
    · norm_num
    · exact ⟨(hp k).1.le, (hp k).2.le⟩
  have hcov := cellCover_of_gaps (φ := φ) (w := w) (s := s) hw hn h0 h1
    (fun _ => K * (q (n j) : ℝ) ^ (-σ)) (by
      intro g hg
      obtain ⟨c1, c2, hlt, hsepg⟩ := mem_cutGaps.1 hg
      have hno : ∀ k < q (n j), φ k ∉ Ioo g.1 g.2 := by
        intro k hk hmem
        have hkC : φ k ∈ C := mem_earlyCuts.2 (Or.inr (Or.inr ⟨k, hk, rfl⟩))
        rcases hsepg _ hkC with h | h
        · linarith [hmem.1]
        · linarith [hmem.2]
      exact hL j hj1 g.1 g.2 (hC01 _ c1).1 hlt (hC01 _ c2).2
        (gap_short_of_approx hfr hq0 (hG.coprime (n j)) (good_approx_sq hG (hmono (Nat.le_succ _)))
          (hC01 _ c1).1 (hC01 _ c2).2 fun k hk => hno k (by omega)) hno)
  refine hcov.mono ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((cutGaps C).card : ℝ) ≤ 3 * q (n j) := by
    have h := (card_cutGaps_le C).trans (card_earlyCuts_le φ (q (n j)))
    have h' : ((cutGaps C).card : ℝ) ≤ q (n j) + 2 := by exact_mod_cast h
    linarith
  have hpow : (q (n j) : ℝ) * (q (n j) : ℝ) ^ (-σ) = (q (n j) : ℝ) ^ (-(σ - 1)) := by
    rw [show -(σ - 1) = 1 + -σ by ring, Real.rpow_add (by linarith), Real.rpow_one]
  calc ((cutGaps C).card : ℝ) * (K * (q (n j) : ℝ) ^ (-σ))
      ≤ 3 * q (n j) * (K * (q (n j) : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 * K * ((q (n j) : ℕ) : ℝ) ^ (-(σ - 1)) := by rw [← hpow]; ring
    _ ≤ ε := hsmall

end Problems.Juggler.BeattySlope
