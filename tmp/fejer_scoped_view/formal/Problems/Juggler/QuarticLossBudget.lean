import Mathlib
import Problems.Juggler.QuarticCells

namespace Problems.Juggler.QuarticLossBudget

open scoped BigOperators

/-- Finite permutation transport cancels the potential at every vertex. -/
theorem defect_sum_of_permutation {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (potential edgeLog defect : ι → ℝ)
    (hdef : ∀ i, defect i = edgeLog i + potential i - potential (next i)) :
    ∑ i, defect i = ∑ i, edgeLog i := by
  calc
    (∑ i, defect i) = ∑ i, (edgeLog i + potential i - potential (next i)) :=
      Finset.sum_congr rfl (fun i _ => hdef i)
    _ = ∑ i, edgeLog i := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp]
      ring

/-- The two branch counts determine the finite component's total formal defect. -/
theorem two_branch_defect_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (upper : Finset ι) (potential defect : ι → ℝ)
    (b A : ℝ)
    (hdef : ∀ i, defect i = (b - if i ∈ upper then A else 0) +
      potential i - potential (next i)) :
    ∑ i, defect i = (Fintype.card ι : ℝ) * b - (upper.card : ℝ) * A := by
  rw [defect_sum_of_permutation next potential _ defect hdef]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_mem]

/-- Finite actual blocks and their injectively chosen replacements. -/
structure BlockSubstitution {α β : Type*} [DecidableEq α]
    (actual : Finset α) (periodic : Finset β)
    (actualDefect : α → ℝ) (formalDefect shift : β → ℝ) where
  partner : β → α
  maps : ∀ i ∈ periodic, partner i ∈ actual
  injective : Set.InjOn partner (↑periodic : Set β)
  defect_eq : ∀ i ∈ periodic,
    actualDefect (partner i) = formalDefect i + shift i
  nonneg : ∀ a ∈ actual, 0 ≤ actualDefect a
  omitted : ∃ a ∈ actual, a ∉ periodic.image partner ∧ 0 < actualDefect a

/-- A positive omitted actual block makes the substitution budget strict. -/
theorem BlockSubstitution.strict_budget {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s) :
    (∑ i ∈ periodic, d i) + (∑ i ∈ periodic, s i) < ∑ a ∈ actual, D a := by
  obtain ⟨a, ha, hnot, hpos⟩ := B.omitted
  have hsub : periodic.image B.partner ⊆ actual := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact B.maps i hi
  have hlt : (∑ j ∈ periodic.image B.partner, D j) < ∑ j ∈ actual, D j :=
    Finset.sum_lt_sum_of_subset hsub ha hnot hpos (fun j hj _ => B.nonneg j hj)
  have heq : (∑ j ∈ periodic.image B.partner, D j) =
      (∑ i ∈ periodic, d i) + (∑ i ∈ periodic, s i) := by
    rw [Finset.sum_image B.injective]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl B.defect_eq
  rwa [heq] at hlt

/-- Reserving disjoint actual towers gives the corresponding non-strict budget. -/
theorem BlockSubstitution.reserved_budget {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (reserved : Finset α) (hreserved : reserved ⊆ actual)
    (hdisjoint : Disjoint (periodic.image B.partner) reserved) :
    (∑ i ∈ periodic, d i) + (∑ i ∈ periodic, s i) +
      (∑ a ∈ reserved, D a) ≤ ∑ a ∈ actual, D a := by
  have hsub : periodic.image B.partner ∪ reserved ⊆ actual := by
    apply Finset.union_subset
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact B.maps i hi
    · exact hreserved
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j hj _ => B.nonneg j hj)
  have heq : (∑ j ∈ periodic.image B.partner, D j) =
      (∑ i ∈ periodic, d i) + (∑ i ∈ periodic, s i) := by
    rw [Finset.sum_image B.injective, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl B.defect_eq
  rwa [Finset.sum_union hdisjoint, heq] at hle

/-- Calibrating the strict component budget produces the signed loss inequality. -/
theorem calibrated_component_budget {e n Λ lam Δ A Γ : ℝ}
    (he : 0 < e) (hbudget : lam - Γ < Λ)
    (hcal : e * lam = n * Λ + Δ * A) :
    Δ * A < (e - n) * Λ + e * Γ := by
  have hm := mul_lt_mul_of_pos_left hbudget he
  nlinarith

/-- The component inequality is derived from the finite actual-block partition. -/
theorem BlockSubstitution.component_budget {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    {e n Λ lam Δ A Γ : ℝ} (he : 0 < e)
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -Γ ≤ ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * A) :
    Δ * A < (e - n) * Λ + e * Γ := by
  have hb := B.strict_budget
  rw [htotal, hformal] at hb
  apply calibrated_component_budget he (by linarith) hcal

/-- Positive displacements turn a strict total gap into a normalized witness. -/
theorem weighted_gap_witness {ι : Type*} (S : Finset ι)
    (displacement gap : ι → ℝ) {Δ τ : ℝ}
    (hτ : 0 ≤ τ) (hd : ∀ i ∈ S, 0 < displacement i)
    (hsum : ∑ i ∈ S, displacement i ≤ Δ)
    (hgap : Δ * τ < ∑ i ∈ S, gap i) :
    ∃ i ∈ S, τ < gap i / displacement i := by
  by_contra! h
  have hpoint : ∀ i ∈ S, gap i ≤ τ * displacement i := by
    intro i hi
    exact (div_le_iff₀ (hd i hi)).mp (h i hi)
  have hbound : (∑ i ∈ S, gap i) ≤ Δ * τ := by
    calc
      (∑ i ∈ S, gap i) ≤ ∑ i ∈ S, τ * displacement i :=
        Finset.sum_le_sum hpoint
      _ = τ * ∑ i ∈ S, displacement i := by rw [Finset.mul_sum]
      _ ≤ τ * Δ := mul_le_mul_of_nonneg_left hsum hτ
      _ = Δ * τ := by ring
  linarith

/-- A unit lower bound and the covered-cell cap identify an uncovered witness. -/
theorem weighted_uncovered_witness {ι : Type*} (S : Finset ι)
    (displacement gap : ι → ℝ) (covered : ι → Prop) {Δ τ η : ℝ}
    (hη : 0 ≤ η) (hητ : η ≤ τ)
    (hd : ∀ i ∈ S, 1 ≤ displacement i)
    (hsum : ∑ i ∈ S, displacement i ≤ Δ)
    (hgap : Δ * τ < ∑ i ∈ S, gap i)
    (hcovered : ∀ i ∈ S, covered i → gap i < η) :
    ∃ i ∈ S, ¬ covered i ∧ τ < gap i / displacement i := by
  obtain ⟨i, hi, hgt⟩ := weighted_gap_witness S displacement gap
    (hη.trans hητ) (fun i hi => lt_of_lt_of_le zero_lt_one (hd i hi)) hsum hgap
  refine ⟨i, hi, ?_, hgt⟩
  intro hc
  have hprod : η ≤ η * displacement i := by
    simpa using mul_le_mul_of_nonneg_left (hd i hi) hη
  have hgi : gap i < η * displacement i := (hcovered i hi hc).trans_le hprod
  have hquot : gap i / displacement i < η :=
    (div_lt_iff₀ (lt_of_lt_of_le zero_lt_one (hd i hi))).mpr hgi
  linarith

/-- The scalar threshold is expressed without any unproved cycle extraction. -/
noncomputable def gapThreshold (e n Λ Δ A : ℝ) : ℝ :=
  (Δ * A - (e - n) * Λ) / (e * Δ)

theorem gapThreshold_eq {e n Λ Δ A : ℝ} (he : 0 < e) (hΔ : 0 < Δ) :
    gapThreshold e n Λ Δ A = A / e - (e - n) * Λ / (e * Δ) := by
  unfold gapThreshold
  field_simp

/-- The small-product hypothesis gives the positive covered-cell threshold. -/
theorem gapThreshold_ge {e n Λ Δ A η : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * η ≤ A) :
    η ≤ gapThreshold e n Λ Δ A := by
  have he0 : 0 < e := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hbase : 0 ≤ (e - 1) * Λ := mul_nonneg (by linarith) hΛ.le
  have h1 : (e - n) * Λ ≤ (e - 1) * Λ :=
    mul_le_mul_of_nonneg_right (by linarith) hΛ.le
  have h2 : (e - 1) * Λ ≤ Δ * ((e - 1) * Λ) := by
    nlinarith
  have h3 : Δ * ((e - 1) * Λ) ≤ Δ * (A - e * η) :=
    mul_le_mul_of_nonneg_left (by linarith) hΔ0.le
  have hc := h1.trans (h2.trans h3)
  unfold gapThreshold
  apply (le_div_iff₀ (mul_pos he0 hΔ0)).mpr
  nlinarith

/-- A calibrated strict budget is the weighted sum threshold used above. -/
theorem gapThreshold_sum_lt {ι : Type*} (S : Finset ι) (gap : ι → ℝ)
    {e n Λ Δ A : ℝ} (he : 0 < e) (hΔ : 0 < Δ)
    (hbudget : Δ * A < (e - n) * Λ + e * ∑ i ∈ S, gap i) :
    Δ * gapThreshold e n Λ Δ A < ∑ i ∈ S, gap i := by
  have hth : e * Δ * gapThreshold e n Λ Δ A = Δ * A - (e - n) * Λ := by
    unfold gapThreshold
    exact mul_div_cancel₀ _ (ne_of_gt (mul_pos he hΔ))
  apply lt_of_mul_lt_mul_left (a := e) _ he.le
  nlinarith

/-- A finite actual-block certificate yields the normalized uncovered witness. -/
theorem BlockSubstitution.uncovered_component_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement gap : β → ℝ) (covered : β → Prop)
    {e n Λ lam Δ A η : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hη : 0 ≤ η) (hsmall : (e - 1) * Λ + e * η ≤ A)
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, gap i) ≤ ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * A)
    (hd : ∀ i ∈ negative, 1 ≤ displacement i)
    (hsum : ∑ i ∈ negative, displacement i ≤ Δ)
    (hcovered : ∀ i ∈ negative, covered i → gap i < η) :
    ∃ i ∈ negative, ¬ covered i ∧
      gapThreshold e n Λ Δ A < gap i / displacement i := by
  have he0 : 0 < e := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hb := B.component_budget he0 htotal hformal hshift hcal
  have hg := gapThreshold_sum_lt negative gap he0 hΔ0 hb
  exact weighted_uncovered_witness negative displacement gap covered hη
    (gapThreshold_ge he hΛ hn hΔ hsmall) hd hsum hg hcovered

/-- If every candidate is covered, the same finite certificate is impossible. -/
theorem BlockSubstitution.not_all_covered {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement gap : β → ℝ)
    {e n Λ lam Δ A η : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hη : 0 ≤ η) (hsmall : (e - 1) * Λ + e * η ≤ A)
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, gap i) ≤ ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * A)
    (hd : ∀ i ∈ negative, 1 ≤ displacement i)
    (hsum : ∑ i ∈ negative, displacement i ≤ Δ)
    (hcovered : ∀ i ∈ negative, gap i < η) : False := by
  obtain ⟨i, hi, hnot, _⟩ := B.uncovered_component_witness negative displacement gap
    (fun _ => True) he hΛ hn hΔ hη hsmall htotal hformal hshift hcal hd hsum
    (fun i hi _ => hcovered i hi)
  exact hnot trivial

/-- The scalar covered-cell contradiction also covers a total component budget. -/
theorem covered_budget_contradiction {e t Λ A η charge harmful : ℝ}
    (he : 2 ≤ e) (hΛ : 0 < Λ) (hη : 0 ≤ η)
    (ht : t ≤ e - 1) (hcharge : 1 ≤ charge) (hcount : harmful ≤ charge)
    (hsmall : (e - 1) * Λ + e * η ≤ A)
    (hbudget : charge * A < t * Λ + e * (harmful * η)) : False := by
  have he0 : 0 ≤ e := by linarith
  have hcap : e * (harmful * η) ≤ e * (charge * η) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hη) he0
  have hpos : 0 < A - e * η := by
    have hp : 0 < (e - 1) * Λ := mul_pos (by linarith) hΛ
    linarith
  have hc : A - e * η ≤ charge * (A - e * η) := by
    nlinarith
  have htΛ : t * Λ ≤ (e - 1) * Λ := mul_le_mul_of_nonneg_right ht hΛ.le
  nlinarith

/-- The numerical source gap used by neighboring-cell substitutions. -/
noncomputable def loglogGap (x y : ℕ) : ℝ :=
  Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ))

/-- Exact integer B cells discharge the covered-gap premise of the finite budget. -/
theorem BlockSubstitution.unequal_cell_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement : β → ℝ) (source predecessor : β → ℕ)
    {m : ℕ} {e n Λ lam Δ : ℝ}
    (hm : 1 < m) (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * QuarticCells.logEta (m : ℝ) ≤ Real.log (3 / 2 : ℝ))
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, loglogGap (source i) (predecessor i)) ≤
      ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * Real.log (3 / 2 : ℝ))
    (hd : ∀ i ∈ negative, 1 ≤ displacement i)
    (hsum : ∑ i ∈ negative, displacement i ≤ Δ)
    (hsource : ∀ i ∈ negative, m ≤ source i)
    (hpredecessor : ∀ i ∈ negative, m ≤ predecessor i)
    (hvalley : ∀ i ∈ negative, m ≤ QuarticCells.B (source i)) :
    ∃ i ∈ negative, QuarticCells.B (source i) ≠ QuarticCells.B (predecessor i) ∧
      gapThreshold e n Λ Δ (Real.log (3 / 2 : ℝ)) <
        loglogGap (source i) (predecessor i) / displacement i := by
  have hη : 0 ≤ QuarticCells.logEta (m : ℝ) :=
    (QuarticCells.logEta_pos (by exact_mod_cast hm)).le
  apply B.uncovered_component_witness negative displacement
    (fun i => loglogGap (source i) (predecessor i))
    (fun i => QuarticCells.B (source i) = QuarticCells.B (predecessor i))
    he hΛ hn hΔ hη hsmall htotal hformal hshift hcal hd hsum
  intro i hi hcell
  simpa only [loglogGap] using QuarticCells.same_cell_loglog_lt_min hm
    (hsource i hi) (hpredecessor i hi) (hvalley i hi) rfl hcell.symm

/-- A projection fixed on selected valleys turns the unequal-cell witness into a hole. -/
theorem BlockSubstitution.unselected_valley_witness {α β : Type*} [DecidableEq α]
    {actual : Finset α} {periodic : Finset β}
    {D : α → ℝ} {d s : β → ℝ}
    (B : BlockSubstitution actual periodic D d s)
    (negative : Finset β) (displacement : β → ℝ) (source predecessor : β → ℕ)
    (selected : Set ℕ) {m : ℕ} {e n Λ lam Δ : ℝ}
    (hm : 1 < m) (he : 2 ≤ e) (hΛ : 0 < Λ) (hn : 1 ≤ n) (hΔ : 1 ≤ Δ)
    (hsmall : (e - 1) * Λ + e * QuarticCells.logEta (m : ℝ) ≤ Real.log (3 / 2 : ℝ))
    (htotal : ∑ a ∈ actual, D a = Λ)
    (hformal : ∑ i ∈ periodic, d i = lam)
    (hshift : -(∑ i ∈ negative, loglogGap (source i) (predecessor i)) ≤
      ∑ i ∈ periodic, s i)
    (hcal : e * lam = n * Λ + Δ * Real.log (3 / 2 : ℝ))
    (hd : ∀ i ∈ negative, 1 ≤ displacement i)
    (hsum : ∑ i ∈ negative, displacement i ≤ Δ)
    (hsource : ∀ i ∈ negative, m ≤ source i)
    (hpredecessor : ∀ i ∈ negative, m ≤ predecessor i)
    (hvalley : ∀ i ∈ negative, m ≤ QuarticCells.B (source i))
    (hfixed : ∀ i ∈ negative, QuarticCells.B (source i) ∈ selected →
      QuarticCells.B (source i) = QuarticCells.B (predecessor i)) :
    ∃ i ∈ negative, QuarticCells.B (source i) ∉ selected ∧
      gapThreshold e n Λ Δ (Real.log (3 / 2 : ℝ)) <
        loglogGap (source i) (predecessor i) / displacement i := by
  obtain ⟨i, hi, hne, hgap⟩ := B.unequal_cell_witness negative displacement source predecessor
    hm he hΛ hn hΔ hsmall htotal hformal hshift hcal hd hsum hsource hpredecessor hvalley
  exact ⟨i, hi, fun hmem => hne (hfixed i hi hmem), hgap⟩

/-- A located lower charge and a pair demand give a signed support bound. -/
theorem located_pair_lower {a b α u v k D : ℝ}
    (ha : α ≤ a) (hb : α ≤ b) (hu : k ≤ u)
    (hv : 0 ≤ v) (hsum : D ≤ u + v) :
    a * k + min a b * (D - k) + α * (u + v - D) ≤ a * u + b * v := by
  have h₁ := mul_nonneg
    (sub_nonneg.mpr (min_le_left a b)) (sub_nonneg.mpr hu)
  have h₂ := mul_nonneg
    (sub_nonneg.mpr (min_le_right a b)) hv
  have h₃ := mul_nonneg
    (sub_nonneg.mpr (le_min ha hb)) (sub_nonneg.mpr hsum)
  nlinarith [h₁, h₂, h₃]

/-- The same located charge gives the corresponding upper support bound. -/
theorem located_pair_upper {a b β u v k D : ℝ}
    (ha : a ≤ β) (hb : b ≤ β) (hu : k ≤ u)
    (hv : 0 ≤ v) (hsum : D ≤ u + v) :
    a * u + b * v ≤ a * k + max a b * (D - k) + β * (u + v - D) := by
  have h₁ := mul_nonneg
    (sub_nonneg.mpr (le_max_left a b)) (sub_nonneg.mpr hu)
  have h₂ := mul_nonneg
    (sub_nonneg.mpr (le_max_right a b)) hv
  have h₃ := mul_nonneg
    (sub_nonneg.mpr (max_le ha hb)) (sub_nonneg.mpr hsum)
  nlinarith [h₁, h₂, h₃]

/-- Summing disjoint pair records retains the exact total residual term. -/
theorem located_pairs_lower {ι : Type*} (S : Finset ι)
    (a b u v k D : ι → ℝ) (α : ℝ)
    (ha : ∀ i ∈ S, α ≤ a i) (hb : ∀ i ∈ S, α ≤ b i)
    (hu : ∀ i ∈ S, k i ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hsum : ∀ i ∈ S, D i ≤ u i + v i) :
    (∑ i ∈ S, (a i * k i + min (a i) (b i) * (D i - k i))) +
        α * ((∑ i ∈ S, (u i + v i)) - ∑ i ∈ S, D i) ≤
      ∑ i ∈ S, (a i * u i + b i * v i) := by
  have h := Finset.sum_le_sum (fun i hi =>
    located_pair_lower (ha i hi) (hb i hi) (hu i hi) (hv i hi) (hsum i hi))
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_add, mul_sub] using h

/-- The finite upper bound uses the same located and flexible charges. -/
theorem located_pairs_upper {ι : Type*} (S : Finset ι)
    (a b u v k D : ι → ℝ) (β : ℝ)
    (ha : ∀ i ∈ S, a i ≤ β) (hb : ∀ i ∈ S, b i ≤ β)
    (hu : ∀ i ∈ S, k i ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i)
    (hsum : ∀ i ∈ S, D i ≤ u i + v i) :
    (∑ i ∈ S, (a i * u i + b i * v i)) ≤
      (∑ i ∈ S, (a i * k i + max (a i) (b i) * (D i - k i))) +
        β * ((∑ i ∈ S, (u i + v i)) - ∑ i ∈ S, D i) := by
  have h := Finset.sum_le_sum (fun i hi =>
    located_pair_upper (ha i hi) (hb i hi) (hu i hi) (hv i hi) (hsum i hi))
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_add, mul_sub] using h

end Problems.Juggler.QuarticLossBudget
