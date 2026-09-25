import Problems.Juggler.BeattySlopeMeasureDim

/-!
# The upper bound `s*(ν)` for every approximation exponent

If `|qα - p| ≤ q^(-ν)` for arbitrarily large `q`, with `ν > 1`, the cluster set
has Hausdorff dimension at most `s*(ν) = 2(√(1+3ν) - 1)/(3ν)`, the positive root
of `3νs² + 4s - 4 = 0`. This improves `2/(2+√ν)`.

Take a continued-fraction level `q` with error `|θ| = |qα - p|` and the next
denominator `N ≥ 1/(2|θ|)`. Cut the circle at the first `E` orbit points. A gap
holding an orbit point of index in `[E, N)` is one of at most `q + 1` gaps, one
for each chain label, and together these carry at most the tail mass from `E`.
Every other gap contains no orbit point of index below `N`, so it is shorter
than `4/N`; the orbit is `|θ|`-separated along blocks of `N` consecutive
indices, so the gap receives at most nine atoms per block and its mass is at
most `27B N^(-3/2)`. With `E = q^a` both parts of the cover cost vanish exactly
when `3νs² + 4s > 4`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- **Block window mass.** A window of length at most `L` that no index below
`N ≥ Q` hits carries atom mass at most `3(L/δ + 1)B/(Q√N)`, when the weights
are at most `B(n+1)^(-3/2)` and the orbit is `δ`-separated along blocks of `Q`
consecutive indices. -/
theorem block_window_mass {φ w : ℕ → ℝ} {α B δ L : ℝ} (hn : ∀ n, 0 ≤ w n) (hB : 0 ≤ B)
    (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ))
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {Q : ℕ} (hQ : 0 < Q)
    (hδ : 0 < δ) (hsep : ∀ m : ℕ, 0 < m → m < Q → ∀ p : ℤ, δ ≤ |(m : ℝ) * α - p|)
    {N : ℕ} (hNQ : Q ≤ N) {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ L)
    (hearly : ∀ k, k < N → φ k ∉ Ioo a b) :
    ∑' n, (if φ n ∈ Ioo a b then w n else 0) ≤
      3 * (L / δ + 1) * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) := by
  classical
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hN0 : 0 < N := lt_of_lt_of_le hQ hNQ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hL : 0 ≤ L := (sub_nonneg.2 hab).trans hlen
  set K := L / δ + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  set v : ℕ → ℝ := fun n => B / ((n : ℝ) + 1) ^ (3/2 : ℝ) with hvdef
  have hv0 (n : ℕ) : 0 ≤ v n := div_nonneg hB (by positivity)
  have hvanti {m n : ℕ} (h : m ≤ n) : v n ≤ v m := by
    apply div_le_div_of_nonneg_left hB (by positivity)
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have : (m : ℝ) ≤ n := by exact_mod_cast h
    linarith
  have hvs : Summable v := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (3/2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.2 (by norm_num)
    have h2 := (summable_nat_add_iff 1).2 h1
    refine (h2.mul_left B).congr fun n => ?_
    simp only [hvdef, div_eq_mul_inv]
    push_cast
    ring_nf
  set f : ℕ → ℝ := fun n => if φ n ∈ Ioo a b then w n else 0 with hfdef
  have hf0 (n : ℕ) : 0 ≤ f n := by simp only [hfdef]; split_ifs <;> simp [hn n]
  have hblock (t : ℕ) : ∑ i ∈ Finset.range Q, f (t + i) ≤ K * v t := by
    have hcount := block_count_le (δ := δ) (L := L) hδ hfr hsep hab hlen t
    calc ∑ i ∈ Finset.range Q, f (t + i)
        = ∑ i ∈ (Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b), w (t + i) := by
          rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b), v t := by
          exact Finset.sum_le_sum fun i _ => (hb _).trans (by
            have := hvanti (Nat.le_add_right t i)
            simp only [hvdef] at this ⊢
            push_cast at this ⊢
            exact this)
      _ = _ * v t := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * v t := mul_le_mul_of_nonneg_right hcount (hv0 t)
  have hblocks (J : ℕ) : ∑ k ∈ Finset.range (J * Q + Q), f (N + k) ≤
      K * v N + K / Q * ∑ k ∈ Finset.range (J * Q), v (N + k) := by
    induction J with
    | zero => simpa using hblock N
    | succ J ih =>
      have hL' : ∑ k ∈ Finset.range ((J + 1) * Q + Q), f (N + k) =
          ∑ k ∈ Finset.range (J * Q + Q), f (N + k) +
            ∑ i ∈ Finset.range Q, f (N + (J * Q + Q + i)) := by
        rw [show (J + 1) * Q + Q = (J * Q + Q) + Q by ring, Finset.sum_range_add]
      have hR : ∑ k ∈ Finset.range ((J + 1) * Q), v (N + k) =
          ∑ k ∈ Finset.range (J * Q), v (N + k) +
            ∑ i ∈ Finset.range Q, v (N + (J * Q + i)) := by
        rw [show (J + 1) * Q = J * Q + Q by ring, Finset.sum_range_add]
      have hb2 : ∑ i ∈ Finset.range Q, f (N + (J * Q + Q + i)) ≤ K * v (N + (J * Q + Q)) := by
        simpa [add_assoc] using hblock (N + (J * Q + Q))
      have hcmp : K * v (N + (J * Q + Q)) ≤
          K / Q * ∑ i ∈ Finset.range Q, v (N + (J * Q + i)) := by
        have : (Q : ℝ) * v (N + (J * Q + Q)) ≤ ∑ i ∈ Finset.range Q, v (N + (J * Q + i)) := by
          have := Finset.card_nsmul_le_sum (Finset.range Q) (fun i => v (N + (J * Q + i)))
            (v (N + (J * Q + Q))) fun i hi => hvanti (by
              have := Finset.mem_range.1 hi; omega)
          simpa using this
        rw [div_mul_eq_mul_div, le_div_iff₀ hQR]
        nlinarith
      rw [hL', hR, mul_add]
      linarith
  have htail (M : ℕ) : ∑ k ∈ Finset.range M, v (N + k) ≤ 2 * B * (N : ℝ) ^ (-(1/2) : ℝ) := by
    have ht := tailMass_le hvs hv0 hB (fun n => le_rfl) hN0
    refine le_trans ?_ ht
    have hs : Summable (fun n => if N ≤ n then v n else 0) :=
      hvs.of_norm_bounded fun n => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hv0 n), hv0 n]
    calc ∑ k ∈ Finset.range M, v (N + k)
        = ∑ n ∈ Finset.range (N + M), if N ≤ n then v n else 0 := by
          rw [Finset.sum_range_add]
          have h0 : ∑ n ∈ Finset.range N, (if N ≤ n then v n else 0) = 0 :=
            Finset.sum_eq_zero fun n hn => by
              rw [if_neg (not_le.2 (Finset.mem_range.1 hn))]
          rw [h0, zero_add]
          exact Finset.sum_congr rfl fun k _ => by rw [if_pos (Nat.le_add_right N k)]
      _ ≤ tailMass v N :=
          hs.sum_le_tsum _ fun n _ => by split_ifs <;> simp [hv0 n]
  have hhead : v N ≤ B / Q * (N : ℝ) ^ (-(1/2) : ℝ) := by
    simp only [hvdef]
    have hNQ' : (Q : ℝ) ≤ N := by exact_mod_cast hNQ
    have h1 : (N : ℝ) ^ (3/2 : ℝ) ≤ ((N : ℝ) + 1) ^ (3/2 : ℝ) :=
      Real.rpow_le_rpow hNR.le (by linarith) (by norm_num)
    have h2 : (N : ℝ) ^ (3/2 : ℝ) = N * (N : ℝ) ^ (1/2 : ℝ) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hNR, Real.rpow_one]
    have h3 : (N : ℝ) ^ (-(1/2) : ℝ) = ((N : ℝ) ^ (1/2 : ℝ))⁻¹ := Real.rpow_neg hNR.le _
    have hsq : 0 < (N : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hNR _
    rw [h3, show B / (Q : ℝ) * ((N : ℝ) ^ (1/2 : ℝ))⁻¹ = B / (Q * (N : ℝ) ^ (1/2 : ℝ)) by
      field_simp]
    apply div_le_div_of_nonneg_left hB (by positivity)
    calc (Q : ℝ) * (N : ℝ) ^ (1/2 : ℝ) ≤ N * (N : ℝ) ^ (1/2 : ℝ) :=
          mul_le_mul_of_nonneg_right hNQ' hsq.le
      _ = _ := h2.symm
      _ ≤ _ := h1
  refine Real.tsum_le_of_sum_range_le hf0 fun M => ?_
  have hsub : ∑ n ∈ Finset.range M, f n ≤ ∑ n ∈ Finset.range (N + (M * Q + Q)), f n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 ?_)
      fun n _ _ => hf0 n
    nlinarith
  have hsplit : ∑ n ∈ Finset.range (N + (M * Q + Q)), f n =
      ∑ k ∈ Finset.range (M * Q + Q), f (N + k) := by
    rw [Finset.sum_range_add]
    have : ∑ n ∈ Finset.range N, f n = 0 := Finset.sum_eq_zero fun n hn => by
      simp only [hfdef, if_neg (hearly n (Finset.mem_range.1 hn))]
    rw [this, zero_add]
  have hB2 := hblocks M
  have hT := htail (M * Q)
  have hfac : 0 ≤ K / (Q : ℝ) := by positivity
  calc ∑ n ∈ Finset.range M, f n ≤ _ := hsub
    _ = _ := hsplit
    _ ≤ K * v N + K / Q * ∑ k ∈ Finset.range (M * Q), v (N + k) := hB2
    _ ≤ K * (B / Q * (N : ℝ) ^ (-(1/2) : ℝ)) + K / Q * (2 * B * (N : ℝ) ^ (-(1/2) : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hhead hK) (mul_le_mul_of_nonneg_left hT hfac)
    _ = 3 * K * B / Q * (N : ℝ) ^ (-(1/2) : ℝ) := by ring

/-- **The sharpened cut estimate.** Gaps of the first `E` orbit points that
hold an orbit point of index in `[E, N)` are at most `q + 1` and together
carry at most the tail mass from `E`; every other gap carries at most
`27B/(N√N)`. -/
theorem star_cut_bound {φ w : ℕ → ℝ} {α B : ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hB : 0 ≤ B) (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ))
    (hi : Function.Injective φ) (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q) (hθ : θ ≠ 0)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN0 : 0 < N) (hN : (N : ℝ) * |θ| ≤ 1) (hNθ : 1 ≤ 2 * (N : ℝ) * |θ|)
    (hsep : ∀ m : ℕ, 0 < m → m < N → ∀ p : ℤ, |θ| ≤ |(m : ℝ) * α - p|)
    (hshort : ∀ c d : ℝ, 0 ≤ c → d ≤ 1 → (∀ k : ℕ, k + 1 < N → φ k ∉ Ioo c d) → d - c ≤ 4 / N)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∀ g ∈ cutGaps (earlyCuts φ E), jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤
      max (tailMass w E) (27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ))) ∧
    ∑ g ∈ cutGaps (earlyCuts φ E), (jumpProfile φ w g.2 - jumpProfileRight φ w g.1) ^ s ≤
      ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s +
        ((E : ℝ) + 2) * (27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s := by
  classical
  set C := earlyCuts φ E
  set G := cutGaps C
  set LN := 27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ) with hLN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have habs : 0 < |θ| := abs_pos.2 hθ
  set mass : ℝ × ℝ → ℝ := fun g => jumpProfile φ w g.2 - jumpProfileRight φ w g.1
  have hsum (R : ℕ → Prop) [DecidablePred R] : Summable (fun n => if R n then w n else 0) :=
    hw.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]
  have hmass0 (g : ℝ × ℝ) (hg : g ∈ G) : 0 ≤ mass g :=
    sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn (mem_cutGaps.1 hg).2.2.1)
  -- atoms inside a gap have index at least `E`
  have hcut (g : ℝ × ℝ) (hg : g ∈ G) (n : ℕ) (h1 : g.1 < φ n) (h2 : φ n < g.2) : E ≤ n := by
    by_contra hlt
    push Not at hlt
    have hC : φ n ∈ C := mem_earlyCuts.2 (Or.inr (Or.inr ⟨n, hlt, rfl⟩))
    rcases (mem_cutGaps.1 hg).2.2.2 _ hC with h | h <;> linarith
  have hmass_tail (g : ℝ × ℝ) (hg : g ∈ G) :
      mass g ≤ ∑' n, if (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n then w n else 0 :=
    jumpGap_mass_le hw hn _ fun n h1 h2 => ⟨⟨h1, h2⟩, hcut g hg n h1 h2⟩
  have htail_le (g : ℝ × ℝ) : (∑' n, if (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n then w n else 0) ≤
      tailMass w E :=
    Summable.tsum_le_tsum (fun n => by
      by_cases h : (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n
      · simp [h]
      · simp only [h, if_false]; split_ifs <;> simp [hn n]) (hsum _) (hsum _)
  -- the gaps in `[0,1]`
  have hC01 : ∀ e ∈ C, 0 ≤ e ∧ e ≤ 1 := by
    intro e he
    rcases mem_earlyCuts.1 he with rfl | rfl | ⟨k, -, rfl⟩
    · norm_num
    · norm_num
    · exact ⟨(hp k).1.le, (hp k).2.le⟩
  -- gaps without a middle atom
  set mid : ℝ × ℝ → Prop := fun g => ∃ n, E ≤ n ∧ n < N ∧ g.1 < φ n ∧ φ n < g.2
  have hlate (g : ℝ × ℝ) (hg : g ∈ G) (hm : ¬ mid g) : mass g ≤ LN := by
    obtain ⟨hg1, hg2, hlt, -⟩ := mem_cutGaps.1 hg
    have hno : ∀ k, k < N → φ k ∉ Ioo g.1 g.2 := by
      intro k hk hk'
      exact hm ⟨k, hcut g hg k hk'.1 hk'.2, hk, hk'.1, hk'.2⟩
    have hlen := hshort g.1 g.2 (hC01 _ hg1).1 (hC01 _ hg2).2 fun k hk => hno k (by omega)
    have hwin := block_window_mass hn hB hb hfr hN0 habs hsep le_rfl hlt.le hlen hno
    have hK : 4 / (N : ℝ) / |θ| + 1 ≤ 9 := by
      have hpos : 0 < (N : ℝ) * |θ| := by positivity
      rw [div_div]
      have : 4 / ((N : ℝ) * |θ|) ≤ 8 := by rw [div_le_iff₀ hpos]; linarith
      linarith
    calc mass g ≤ ∑' n, (if φ n ∈ Ioo g.1 g.2 then w n else 0) :=
          jumpGap_mass_le hw hn _ fun n h1 h2 => ⟨h1, h2⟩
      _ ≤ 3 * (4 / (N : ℝ) / |θ| + 1) * B / N * (N : ℝ) ^ (-(1/2) : ℝ) := hwin
      _ ≤ LN := by
          simp only [hLN]
          have hx : 0 ≤ B / (N : ℝ) * (N : ℝ) ^ (-(1/2) : ℝ) := by positivity
          have e1 : 3 * (4 / (N : ℝ) / |θ| + 1) * B / N * (N : ℝ) ^ (-(1/2) : ℝ) =
              3 * (4 / (N : ℝ) / |θ| + 1) * (B / N * (N : ℝ) ^ (-(1/2) : ℝ)) := by ring
          have e2 : 27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ) = 27 * (B / N * (N : ℝ) ^ (-(1/2) : ℝ)) := by
            ring
          rw [e1, e2]
          nlinarith
  -- the middle gaps
  set Gm := G.filter mid
  have hGm_card : (Gm.card : ℝ) ≤ (q : ℝ) + 1 := by
    let lab : ℝ × ℝ → ℤ := fun g => if h : mid g then
      Z (Classical.choose (p := fun n => E ≤ n ∧ n < N ∧ g.1 < φ n ∧ φ n < g.2) h) else 0
    have hmaps : ∀ g ∈ Gm, lab g ∈ Finset.Icc (0 : ℤ) q := by
      intro g hg
      have hm := (Finset.mem_filter.1 hg).2
      simp only [lab, dif_pos hm]
      obtain ⟨-, hnN, -, -⟩ := Classical.choose_spec (p := fun n => E ≤ n ∧ n < N ∧ g.1 < φ n ∧ φ n < g.2) hm
      apply chain_label_mem hq hφ hp
      have : ((Classical.choose (p := fun n : ℕ => E ≤ n ∧ n < N ∧ g.1 < φ n ∧ φ n < g.2) hm : ℕ) : ℝ) + 1 ≤ N := by
        exact_mod_cast hnN
      exact (mul_le_mul_of_nonneg_right this (abs_nonneg θ)).trans hN
    have hinj : Set.InjOn lab Gm := by
      intro g hg g' hg' heq
      have hm := (Finset.mem_filter.1 hg).2
      have hm' := (Finset.mem_filter.1 hg').2
      simp only [lab, dif_pos hm, dif_pos hm'] at heq
      obtain ⟨hE1, hN1, a1, a2⟩ := Classical.choose_spec (p := fun n => E ≤ n ∧ n < N ∧ g.1 < φ n ∧ φ n < g.2) hm
      obtain ⟨hE2, hN2, b1, b2⟩ := Classical.choose_spec (p := fun n => E ≤ n ∧ n < N ∧ g'.1 < φ n ∧ φ n < g'.2) hm'
      exact chain_same_gap hi hp hq hθ hφ hN (Finset.mem_filter.1 hg).1
        (Finset.mem_filter.1 hg').1 hE1 hN1 hE2 hN2 heq a1 a2 b1 b2
    have := Finset.card_le_card_of_injOn lab hmaps hinj
    have hc : ((Finset.Icc (0 : ℤ) q).card : ℝ) = (q : ℝ) + 1 := by simp
    rw [← hc]
    exact_mod_cast this
  have hGm_sum : ∑ g ∈ Gm, mass g ≤ tailMass w E := by
    calc ∑ g ∈ Gm, mass g
        ≤ ∑ g ∈ Gm, ∑' n, (if (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n then w n else 0) :=
          Finset.sum_le_sum fun g hg => hmass_tail g (Finset.mem_filter.1 hg).1
      _ ≤ ∑' n, if E ≤ n then w n else 0 :=
          sum_tsum_le_of_disjoint Gm hw hn (fun g n => (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n)
            (fun n => E ≤ n)
            (fun n g hg g' hg' h h' => cutGap_eq_of_mem (Finset.mem_filter.1 hg).1
              (Finset.mem_filter.1 hg').1 h.1 h'.1) (fun g _ n h => h.2)
      _ = tailMass w E := rfl
  have hcardG : (G.card : ℝ) ≤ (E : ℝ) + 2 := by
    exact_mod_cast (card_cutGaps_le C).trans (card_earlyCuts_le φ E)
  have hLN0 : 0 ≤ LN := by simp only [hLN]; positivity
  refine ⟨fun g hg => ?_, ?_⟩
  · by_cases hm : mid g
    · exact ((hmass_tail g hg).trans (htail_le g)).trans (le_max_left _ _)
    · exact (hlate g hg hm).trans (le_max_right _ _)
  · rw [← Finset.sum_filter_add_sum_filter_not G mid]
    have h1 : ∑ g ∈ Gm, mass g ^ s ≤ ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s := by
      calc ∑ g ∈ Gm, mass g ^ s ≤ (Gm.card : ℝ) ^ (1 - s) * (∑ g ∈ Gm, mass g) ^ s :=
            sum_rpow_le_card_mul _ (fun g hg => hmass0 g (Finset.mem_filter.1 hg).1) hs hs1
        _ ≤ _ := mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hGm_card (by linarith))
            (Real.rpow_le_rpow (Finset.sum_nonneg fun g hg =>
              hmass0 g (Finset.mem_filter.1 hg).1) hGm_sum hs.le)
            (Real.rpow_nonneg (Finset.sum_nonneg fun g hg =>
              hmass0 g (Finset.mem_filter.1 hg).1) _) (Real.rpow_nonneg (by positivity) _)
    have h2 : ∑ g ∈ G.filter (fun g => ¬ mid g), mass g ^ s ≤ ((E : ℝ) + 2) * LN ^ s := by
      calc ∑ g ∈ G.filter (fun g => ¬ mid g), mass g ^ s
          ≤ ∑ g ∈ G.filter (fun g => ¬ mid g), LN ^ s :=
            Finset.sum_le_sum fun g hg => Real.rpow_le_rpow
              (hmass0 g (Finset.mem_filter.1 hg).1)
              (hlate g (Finset.mem_filter.1 hg).1 (Finset.mem_filter.1 hg).2) hs.le
        _ = ((G.filter (fun g => ¬ mid g)).card : ℝ) * LN ^ s := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((E : ℝ) + 2) * LN ^ s := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLN0 _)
            exact (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans hcardG
    exact add_le_add h1 h2

/-- The threshold `s*(ν) = 2(√(1+3ν) - 1)/(3ν)`. -/
noncomputable def starDim (ν : ℝ) : ℝ := 2 * (Real.sqrt (1 + 3 * ν) - 1) / (3 * ν)

/-- Above the threshold, `3νs² + 4s > 4`. -/
theorem starDim_quad {ν s : ℝ} (hν : 0 < ν) (hs : starDim ν < s) :
    4 * (1 - s) < 3 * ν * s ^ 2 := by
  have h3 : 0 < 3 * ν := by positivity
  have hsq : 0 ≤ Real.sqrt (1 + 3 * ν) := Real.sqrt_nonneg _
  have hsq2 : Real.sqrt (1 + 3 * ν) ^ 2 = 1 + 3 * ν := Real.sq_sqrt (by linarith)
  have h1 : 2 * (Real.sqrt (1 + 3 * ν) - 1) < 3 * ν * s := by
    unfold starDim at hs; rwa [div_lt_iff₀ h3, mul_comm s] at hs
  have h2 : 2 * Real.sqrt (1 + 3 * ν) < 3 * ν * s + 2 := by linarith
  have h4 : (2 * Real.sqrt (1 + 3 * ν)) ^ 2 < (3 * ν * s + 2) ^ 2 :=
    pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
  nlinarith

/-- The threshold is positive. -/
theorem starDim_pos {ν : ℝ} (hν : 0 < ν) : 0 < starDim ν := by
  unfold starDim
  have : 1 < Real.sqrt (1 + 3 * ν) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith
  have : 0 < 3 * ν := by positivity
  positivity

/-- **The `s*(ν)` upper bound, measure form.** If `|qα - p| ≤ q^(-ν)` for
arbitrarily large `q`, with `ν > 1`, then `H^s(K_α) = 0` for every
`s*(ν) < s ≤ 1`. -/
theorem dio_star_hausdorff {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν))
    {s : ℝ} (hs : starDim ν < s) (hs1 : s ≤ 1) :
    Measure.hausdorffMeasure s (passageClusterSet (1/α)) = 0 := by
  classical
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have hs0 : 0 < s := (starDim_pos (by linarith)).trans hs
  have hquad := starDim_quad (by linarith) hs
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
  -- exponents
  set a := (2 * (1 - s) / s + 3 * ν * s / 2) / 2 with hadef
  have hgap : 2 * (1 - s) / s < 3 * ν * s / 2 := by
    rw [div_lt_div_iff₀ hs0 (by norm_num)]
    nlinarith
  have ha1 : 2 * (1 - s) / s < a := by rw [hadef]; linarith
  have ha2 : a < 3 * ν * s / 2 := by rw [hadef]; linarith
  have ha0 : 0 < a := lt_of_le_of_lt (div_nonneg (by linarith) hs0.le) ha1
  set m1 := a * s / 2 - (1 - s) with hm1
  have hm1p : 0 < m1 := by
    have := mul_lt_mul_of_pos_right ha1 hs0
    rw [div_mul_cancel₀ _ hs0.ne'] at this
    rw [hm1]; linarith
  set m2 := 3 * ν * s / 2 - a with hm2
  have hm2p : 0 < m2 := by rw [hm2]; linarith
  -- constants
  set C1 := 2 * (2 * B) ^ s
  set C2 := 4 * (27 * B * 2 ^ (3/2 : ℝ)) ^ s
  apply jumpRange_hausdorff_zero hw hn hi hp hs0
  intro ε hε
  have tq : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have lim (y : ℝ) (hy : 0 < y) (C : ℝ) :
      Tendsto (fun q : ℕ => C * (q : ℝ) ^ (-y)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hy).comp tq).const_mul C
  have ev1 := (lim m1 hm1p C1).eventually (ge_mem_nhds (half_pos hε))
  have ev2 := (lim m2 hm2p C2).eventually (ge_mem_nhds (half_pos hε))
  have ev3 := (lim (a / 2) (by positivity) (2 * B)).eventually (ge_mem_nhds hε)
  have ev4 := (lim (3 * ν / 2) (by positivity) (27 * B * 2 ^ (3/2 : ℝ))).eventually
    (ge_mem_nhds hε)
  have ev5 : ∀ᶠ q : ℕ in atTop, (1 : ℝ) ≤ q := tq.eventually_ge_atTop 1
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.1 (ev1.and (ev2.and (ev3.and (ev4.and ev5))))
  -- a continued-fraction level
  set dg := cfDigits α
  have hdg : ∀ k, 1 ≤ dg (k + 1) := cfDigits_succ_ge hα
  have hLim : cfLim dg = α := cfLim_cfDigits hα hα0.le
  have hG := irrational_goodConvergents hα hα0.le
  obtain ⟨n, hnQ, hqν⟩ := good_cf_level hα hα0 (by linarith) happ Q₀
  set q := cfDen dg (n + 1)
  set p : ℤ := (cfNum dg (n + 1) : ℤ)
  set N := cfDen dg (n + 1 + 1)
  set θ := (q : ℝ) * α - p with hθdef
  obtain ⟨h1, h2, h3, h4, hq1⟩ := hQ₀ q hnQ.le
  have hqR : (0 : ℝ) < q := by linarith
  have hq0 : 0 < q := by exact_mod_cast hqR
  have hN0 : 0 < N := cfDen_succ_pos hdg (n + 1)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hθerr : |θ| = cfErr dg (n + 1) := by
    rw [← abs_cf_err hdg (n + 1), hLim]
    simp [θ, p, q]
  have hθpos : 0 < |θ| := by rw [hθerr]; exact cfErr_pos hdg _
  have hθ : θ ≠ 0 := abs_pos.1 hθpos
  have hN : (N : ℝ) * |θ| ≤ 1 := by
    have := cfErr_le hdg (n + 1)
    rw [hθerr, mul_comm, ← le_div_iff₀ hNR]
    simpa using this
  have hNθ : 1 ≤ 2 * (N : ℝ) * |θ| := by
    have := cfErr_ge hdg (n + 1)
    rw [hθerr]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hsep : ∀ m : ℕ, 0 < m → m < N → ∀ p' : ℤ, |θ| ≤ |(m : ℝ) * α - p'| := by
    intro m hm hmN p'
    rw [hθerr, ← hLim]
    exact cf_best_approx hdg (n + 1) m hm hmN p'
  have hshort : ∀ c d : ℝ, 0 ≤ c → d ≤ 1 → (∀ k : ℕ, k + 1 < N → φ k ∉ Ioo c d) →
      d - c ≤ 4 / N := by
    intro c d hc hd hno
    have hcop := hG.coprime (n + 1)
    have happr : |α - (cfNum dg (n + 1 + 1) : ℤ) / (N : ℝ)| ≤ 1 / (N : ℝ) ^ 2 := by
      have h := hG.approx (n + 1)
      have hmono : (N : ℝ) ≤ cfDen dg (n + 1 + 1 + 1) := by
        exact_mod_cast cfDen_le_succ hdg (n + 1 + 1)
      have h' : |(N : ℝ) * α - (cfNum dg (n + 1 + 1) : ℤ)| ≤ 1 / (N : ℝ) := by
        refine h.trans ?_
        exact one_div_le_one_div_of_le hNR hmono
      have e : α - ((cfNum dg (n + 1 + 1) : ℤ) : ℝ) / N =
          ((N : ℝ) * α - (cfNum dg (n + 1 + 1) : ℤ)) / N := by field_simp
      rw [e, abs_div, abs_of_pos hNR, div_le_iff₀ hNR]
      calc _ ≤ 1 / (N : ℝ) := h'
        _ = 1 / (N : ℝ) ^ 2 * N := by field_simp
    exact gap_short_of_approx hfr hN0 hcop happr hc hd hno
  let Z : ℕ → ℤ := fun k => ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ := by
    intro k
    rw [hfr k, Int.fract]
    simp only [Z, θ]
    push_cast
    ring
  -- sizes
  have hθle : |θ| ≤ (q : ℝ) ^ (-ν) := by simpa [θ, p] using hqν
  have hNlow : (q : ℝ) ^ ν / 2 ≤ N := by
    have e1 : (q : ℝ) ^ ν * (q : ℝ) ^ (-ν) = 1 := by rw [← Real.rpow_add hqR]; simp
    have h5 : (q : ℝ) ^ ν * |θ| ≤ 1 := by
      calc _ ≤ (q : ℝ) ^ ν * (q : ℝ) ^ (-ν) :=
            mul_le_mul_of_nonneg_left hθle (by positivity)
        _ = 1 := e1
    have h6 : (q : ℝ) ^ ν * |θ| ≤ 2 * N * |θ| := by linarith
    have := le_of_mul_le_mul_right h6 hθpos
    linarith
  set E := ⌈(q : ℝ) ^ a⌉₊
  have hqa : 1 ≤ (q : ℝ) ^ a := Real.one_le_rpow hq1 ha0.le
  have hE1 : (q : ℝ) ^ a ≤ E := Nat.le_ceil _
  have hE2 : (E : ℝ) < (q : ℝ) ^ a + 1 := Nat.ceil_lt_add_one (by positivity)
  have hER : (0 : ℝ) < E := by linarith
  have hE0 : 0 < E := by exact_mod_cast hER
  obtain ⟨hdiam, hsum⟩ := star_cut_bound hw hn hB.le hb hi hp hfr hq0 hθ hφ hN0 hN hNθ hsep
    hshort (E := E) hs0 hs1
  have hTE := tailMass_le hw hn hB.le hb hE0
  have hEpow : (E : ℝ) ^ (-(1/2) : ℝ) ≤ (q : ℝ) ^ (-(a / 2)) := by
    calc (E : ℝ) ^ (-(1/2) : ℝ) ≤ ((q : ℝ) ^ a) ^ (-(1/2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hE1 (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hqR.le]; ring_nf
  have hT : tailMass w E ≤ 2 * B * (q : ℝ) ^ (-(a / 2)) :=
    hTE.trans (mul_le_mul_of_nonneg_left hEpow (by positivity))
  -- the late gap bound
  set X := (q : ℝ) ^ ν / 2
  have hX : 0 < X := by positivity
  have hLN : 27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ) ≤ 27 * B * 2 ^ (3/2 : ℝ) * (q : ℝ) ^ (-(3 * ν / 2)) := by
    have hNi : (1 : ℝ) / N ≤ 1 / X := one_div_le_one_div_of_le hX hNlow
    have hNh : (N : ℝ) ^ (-(1/2) : ℝ) ≤ X ^ (-(1/2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX hNlow (by norm_num)
    have eX : 1 / X * X ^ (-(1/2) : ℝ) = 2 ^ (3/2 : ℝ) * (q : ℝ) ^ (-(3 * ν / 2)) := by
      have e1 : 1 / X = X ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, one_div]
      rw [e1, ← Real.rpow_add hX, show -(1 : ℝ) + -(1/2) = -(3/2) by norm_num]
      simp only [X]
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hqR.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring_nf
    calc 27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ) = 27 * B * (1 / N * (N : ℝ) ^ (-(1/2) : ℝ)) := by ring
      _ ≤ 27 * B * (1 / X * X ^ (-(1/2) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hNi hNh (by positivity) (by positivity)
      _ = _ := by rw [eX]; ring
  refine ⟨earlyCuts φ E, by simp [earlyCuts], by simp [earlyCuts], fun g hg => ?_, hsum.trans ?_⟩
  · refine (hdiam g hg).trans (max_le ?_ ?_)
    · exact hT.trans h3
    · exact hLN.trans h4
  · -- first term
    have hq2 : (q : ℝ) + 1 ≤ 2 * q := by linarith
    have t1 : ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s ≤ C1 * (q : ℝ) ^ (-m1) := by
      have hTs : tailMass w E ^ s ≤ (2 * B) ^ s * (q : ℝ) ^ (-(a / 2) * s) := by
        calc tailMass w E ^ s ≤ (2 * B * (q : ℝ) ^ (-(a / 2))) ^ s :=
              Real.rpow_le_rpow (tailMass_nonneg hn E) hT hs0.le
          _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hqR.le]
      have hQs : ((q : ℝ) + 1) ^ (1 - s) ≤ 2 * (q : ℝ) ^ (1 - s) := by
        calc ((q : ℝ) + 1) ^ (1 - s) ≤ (2 * q) ^ (1 - s) :=
              Real.rpow_le_rpow (by positivity) hq2 (by linarith)
          _ = 2 ^ (1 - s) * (q : ℝ) ^ (1 - s) := Real.mul_rpow (by norm_num) hqR.le
          _ ≤ 2 * (q : ℝ) ^ (1 - s) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (2 : ℝ) ^ (1 - s) ≤ 2 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 := Real.rpow_one 2
      calc ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s
          ≤ (2 * (q : ℝ) ^ (1 - s)) * ((2 * B) ^ s * (q : ℝ) ^ (-(a / 2) * s)) :=
            mul_le_mul hQs hTs (Real.rpow_nonneg (tailMass_nonneg hn E) s) (by positivity)
        _ = C1 * ((q : ℝ) ^ (1 - s) * (q : ℝ) ^ (-(a / 2) * s)) := by ring
        _ = C1 * (q : ℝ) ^ (-m1) := by
            rw [← Real.rpow_add hqR]; congr 2; rw [hm1]; ring
    -- second term
    have t2 : ((E : ℝ) + 2) * (27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s ≤ C2 * (q : ℝ) ^ (-m2) := by
      have hE4 : (E : ℝ) + 2 ≤ 4 * (q : ℝ) ^ a := by linarith
      have hLs : (27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s ≤
          (27 * B * 2 ^ (3/2 : ℝ)) ^ s * (q : ℝ) ^ (-(3 * ν / 2) * s) := by
        calc _ ≤ (27 * B * 2 ^ (3/2 : ℝ) * (q : ℝ) ^ (-(3 * ν / 2))) ^ s :=
              Real.rpow_le_rpow (by positivity) hLN hs0.le
          _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hqR.le]
      calc ((E : ℝ) + 2) * (27 * B / N * (N : ℝ) ^ (-(1/2) : ℝ)) ^ s
          ≤ (4 * (q : ℝ) ^ a) * ((27 * B * 2 ^ (3/2 : ℝ)) ^ s * (q : ℝ) ^ (-(3 * ν / 2) * s)) :=
            mul_le_mul hE4 hLs (by positivity) (by positivity)
        _ = C2 * ((q : ℝ) ^ a * (q : ℝ) ^ (-(3 * ν / 2) * s)) := by ring
        _ = C2 * (q : ℝ) ^ (-m2) := by
            rw [← Real.rpow_add hqR]; congr 2; rw [hm2]; ring
    linarith

/-- **The `s*(ν)` upper bound.** If `|qα - p| ≤ q^(-ν)` for arbitrarily large
`q`, with `ν > 1`, the cluster set has Hausdorff dimension at most
`s*(ν) = 2(√(1+3ν) - 1)/(3ν)`. -/
theorem dio_star_dimH_le {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν)) :
    dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (starDim ν) := by
  have hν0 : 0 < ν := by linarith
  have hD0 : 0 ≤ starDim ν := (starDim_pos hν0).le
  have hD1 : starDim ν < 1 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < 3 * ν := by positivity
    unfold starDim at hc
    rw [le_div_iff₀ hpos] at hc
    have hs : Real.sqrt (1 + 3 * ν) < 1 + 3 * ν / 2 := by
      rw [Real.sqrt_lt' (by positivity)]
      nlinarith
    linarith
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  by_cases hct : c = ⊤
  · rw [hct]; exact le_top
  set r := c.toReal
  have hcr : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hct).symm
  have hr : starDim ν < r := by
    rw [hcr] at hc
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hc).1
  set s := min r 1
  have hs : starDim ν < s := lt_min hr hD1
  have hs1 : s ≤ 1 := min_le_right _ _
  have hs0 : 0 ≤ s := hD0.trans hs.le
  have hH := dio_star_hausdorff hα1 hα hν happ hs hs1
  have h1 : dimH (passageClusterSet (1/α)) ≤ (s.toNNReal : ℝ≥0∞) := by
    apply dimH_le_of_hausdorffMeasure_ne_top
    rw [Real.coe_toNNReal _ hs0, hH]
    exact ENNReal.zero_ne_top
  refine h1.trans ?_
  rw [hcr, ← ENNReal.ofReal]
  exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

end Problems.Juggler.BeattySlope
