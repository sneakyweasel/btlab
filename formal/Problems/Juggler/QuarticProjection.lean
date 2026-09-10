import Mathlib

namespace Problems.Juggler.QuarticProjection

open scoped BigOperators

/-- The last selected anchor at or before an integer rank. -/
def predecessor (anchors : Finset ℕ) (i : ℕ) : ℕ :=
  (anchors.filter (fun a => a ≤ i)).sup id

theorem predecessor_le (anchors : Finset ℕ) (i : ℕ) :
    predecessor anchors i ≤ i := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.mem_filter.mp ha).2

theorem predecessor_monotone (anchors : Finset ℕ) : Monotone (predecessor anchors) := by
  intro i j hij
  apply Finset.sup_le
  intro a ha
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
    ((Finset.mem_filter.mp ha).2).trans hij⟩

theorem predecessor_eq_self (anchors : Finset ℕ) {i : ℕ} (hi : i ∈ anchors) :
    predecessor anchors i = i := by
  apply le_antisymm (predecessor_le anchors i)
  exact Finset.le_sup (s := anchors.filter (fun a => a ≤ i)) (f := id)
    (Finset.mem_filter.mpr ⟨hi, le_rfl⟩)

theorem predecessor_mem (anchors : Finset ℕ) (hzero : 0 ∈ anchors) (i : ℕ) :
    predecessor anchors i ∈ anchors := by
  have hn : (anchors.filter (fun a => a ≤ i)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨hzero, Nat.zero_le i⟩⟩
  have hm := Finset.sup_mem_of_nonempty (f := id) hn
  obtain ⟨a, ha, he⟩ := hm
  dsimp only [id_eq] at he
  change (anchors.filter (fun a => a ≤ i)).sup id ∈ anchors
  rw [← he]
  exact (Finset.mem_filter.mp ha).1

/-- The predecessor is constant until the next selected anchor. -/
theorem predecessor_eq_on_cell (anchors : Finset ℕ) {a i : ℕ}
    (ha : a ∈ anchors) (hai : a ≤ i)
    (hgap : ∀ b ∈ anchors, b ≤ i → b ≤ a) :
    predecessor anchors i = a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    exact hgap b (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  · exact Finset.le_sup (s := anchors.filter (fun b => b ≤ i)) (f := id)
      (Finset.mem_filter.mpr ⟨ha, hai⟩)

/-- An embedded finite periodic component together with its exact rank lift. -/
structure RankComponent (ι : Type*) [Fintype ι] [DecidableEq ι] (e s : ℕ) where
  rank : ι → ℕ
  rank_lt : ∀ i, rank i < e
  rank_injective : Function.Injective rank
  next : Equiv.Perm ι
  collapse : ℕ → ℕ
  collapse_le : ∀ i, collapse (rank i) ≤ rank i
  upper : Finset ι
  lift_eq : ∀ i,
    rank (next i) + e * (if i ∈ upper then 1 else 0) = collapse (rank i) + s

namespace RankComponent

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {e s : ℕ}

/-- A modular two-block return determines its exact zero-or-one wrap lift. -/
def ofModular {r : ℕ} (he : e = r + s)
    (rank : ι → ℕ) (hrank : ∀ i, rank i < e)
    (hinj : Function.Injective rank) (σ : Equiv.Perm ι) (f : ℕ → ℕ)
    (hle : ∀ i, f (rank i) ≤ rank i)
    (hupper : ∀ i, r ≤ rank i → f (rank i) = rank i)
    (hstep : ∀ i, rank (σ i) = (f (rank i) + s) % e) :
    RankComponent ι e s where
  rank := rank
  rank_lt := hrank
  rank_injective := hinj
  next := σ
  collapse := f
  collapse_le := hle
  upper := Finset.univ.filter (fun i => r ≤ rank i)
  lift_eq := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : r ≤ rank i
    · have hsub : rank i + s = e + (rank i - r) := by omega
      have hsmall : rank i - r < e := (Nat.sub_le _ _).trans_lt (hrank i)
      have hnext : rank (σ i) = rank i - r := by
        rw [hstep i, hupper i hi, hsub]
        simp [Nat.mod_eq_of_lt hsmall]
      rw [if_pos hi, hnext, hupper i hi]
      omega
    · have hsmall : f (rank i) + s < e := by
        have hh := hle i
        omega
      rw [if_neg hi, hstep i, Nat.mod_eq_of_lt hsmall]
      omega

def displacement (C : RankComponent ι e s) (i : ι) : ℕ :=
  C.rank i - C.collapse (C.rank i)

def totalDisplacement (C : RankComponent ι e s) : ℕ :=
  ∑ i, C.displacement i

theorem displacement_add_collapse (C : RankComponent ι e s) (i : ι) :
    C.displacement i + C.collapse (C.rank i) = C.rank i := by
  exact Nat.sub_add_cancel (C.collapse_le i)

/-- The periodic permutation cancels rank coordinates in the summed lift. -/
theorem displacement_balance (C : RankComponent ι e s) :
    C.totalDisplacement + e * C.upper.card = s * Fintype.card ι := by
  have hp : ∀ i, C.rank (C.next i) +
      e * (if i ∈ C.upper then 1 else 0) + C.displacement i = C.rank i + s := by
    intro i
    have h := C.lift_eq i
    have hd := C.displacement_add_collapse i
    omega
  have hs := congrArg (fun f : ι → ℕ => ∑ i, f i) (funext hp)
  have he : (∑ i, C.rank (C.next i)) = ∑ i, C.rank i := Equiv.sum_comp C.next C.rank
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
  rw [he, Nat.mul_comm (Fintype.card ι) s] at hs
  dsimp [totalDisplacement]
  omega

theorem displacement_eq_sub (C : RankComponent ι e s) :
    C.totalDisplacement = s * Fintype.card ι - e * C.upper.card := by
  have h := C.displacement_balance
  omega

theorem dvd_totalDisplacement (C : RankComponent ι e s) {d : ℕ}
    (he : d ∣ e) (hs : d ∣ s) : d ∣ C.totalDisplacement := by
  obtain ⟨u, hu⟩ := he
  obtain ⟨v, hv⟩ := hs
  refine ⟨v * Fintype.card ι - u * C.upper.card, ?_⟩
  rw [C.displacement_eq_sub]
  simp only [hu, hv, Nat.mul_sub, Nat.mul_assoc]

theorem gcd_dvd_totalDisplacement (C : RankComponent ι e s) :
    Nat.gcd e s ∣ C.totalDisplacement :=
  C.dvd_totalDisplacement (Nat.gcd_dvd_left e s) (Nat.gcd_dvd_right e s)

theorem turn_count_le (C : RankComponent ι e s) :
    e * C.upper.card ≤ s * Fintype.card ι := by
  have h := C.displacement_balance
  omega

theorem totalDisplacement_eq_zero_iff (C : RankComponent ι e s) :
    C.totalDisplacement = 0 ↔ ∀ i, C.collapse (C.rank i) = C.rank i := by
  constructor
  · intro h i
    have hz : C.displacement i = 0 := by
      have hle : C.displacement i ≤ C.totalDisplacement :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hle := C.collapse_le i
    dsimp [displacement] at hz
    omega
  · intro h
    simp [totalDisplacement, displacement, h]

/-- A genuine omitted ambient rank makes the embedded component smaller. -/
theorem card_lt_of_omitted (C : RankComponent ι e s) {j : ℕ}
    (hj : j < e) (homit : ∀ i, C.rank i ≠ j) : Fintype.card ι < e := by
  have hsub : Finset.univ.image C.rank ⊆ Finset.range e := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr (C.rank_lt i)
  have hproper : Finset.univ.image C.rank ⊂ Finset.range e := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hm : j ∈ Finset.univ.image C.rank := by
      rw [heq]
      exact Finset.mem_range.mpr hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    exact homit i hi
  have hc := Finset.card_lt_card hproper
  simpa only [Finset.card_image_of_injective _ C.rank_injective,
    Finset.card_univ, Finset.card_range] using hc

/-- Coprime ambient rotation excludes zero loss on a nonempty proper component. -/
theorem totalDisplacement_pos_of_coprime (C : RankComponent ι e s)
    [Nonempty ι] (hcop : Nat.Coprime e s) (hn : Fintype.card ι < e) :
    0 < C.totalDisplacement := by
  by_contra hpos
  have hz : C.totalDisplacement = 0 := by omega
  have hb := C.displacement_balance
  rw [hz, zero_add] at hb
  have hd : e ∣ s * Fintype.card ι := ⟨C.upper.card, hb.symm⟩
  have hdn : e ∣ Fintype.card ι := hcop.dvd_mul_left.mp hd
  have hp : 0 < Fintype.card ι := Fintype.card_pos
  have hle := Nat.le_of_dvd hp hdn
  omega

theorem totalDisplacement_pos_of_omitted (C : RankComponent ι e s)
    [Nonempty ι] (hcop : Nat.Coprime e s) {j : ℕ}
    (hj : j < e) (homit : ∀ i, C.rank i ≠ j) :
    0 < C.totalDisplacement :=
  C.totalDisplacement_pos_of_coprime hcop (C.card_lt_of_omitted hj homit)

theorem displacement_pos_iff (C : RankComponent ι e s) (i : ι) :
    0 < C.displacement i ↔ C.collapse (C.rank i) < C.rank i := by
  simp [displacement]

theorem selected_displacement_le (C : RankComponent ι e s) (S : Finset ι) :
    ∑ i ∈ S, C.displacement i ≤ C.totalDisplacement := by
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- Every selected negative substitution spends at least one rank unit. -/
theorem negative_card_le (C : RankComponent ι e s) (S : Finset ι)
    (hneg : ∀ i ∈ S, C.collapse (C.rank i) < C.rank i) :
    S.card ≤ C.totalDisplacement := by
  calc
    S.card = ∑ _i ∈ S, 1 := by simp
    _ ≤ ∑ i ∈ S, C.displacement i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (C.displacement_pos_iff i).2 (hneg i hi)
      omega
    _ ≤ C.totalDisplacement := C.selected_displacement_le S

/-- A partner after the block start cannot increase the charged interval length. -/
theorem partner_interval_sum_le (C : RankComponent ι e s) (S : Finset ι)
    (partnerRank : ι → ℕ)
    (hstart : ∀ i ∈ S, C.collapse (C.rank i) ≤ partnerRank i) :
    ∑ i ∈ S, (C.rank i - partnerRank i) ≤ C.totalDisplacement := by
  calc
    _ ≤ ∑ i ∈ S, C.displacement i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := hstart i hi
      dsimp [displacement]
      omega
    _ ≤ C.totalDisplacement := C.selected_displacement_le S

theorem selected_displacement_cast_le (C : RankComponent ι e s) (S : Finset ι) :
    ∑ i ∈ S, (C.displacement i : ℝ) ≤ (C.totalDisplacement : ℝ) := by
  exact_mod_cast C.selected_displacement_le S

end RankComponent

/-- Equal projected targets make a chosen partner map injective on a periodic set. -/
theorem partner_injOn {α β γ : Type*} {P : Set α}
    {T : α → γ} {R : β → γ} {partner : α → β}
    (hT : Set.InjOn T P)
    (hpartner : ∀ x ∈ P, R (partner x) = T x) :
    Set.InjOn partner P := by
  intro x hx y hy hxy
  apply hT hx hy
  rw [← hpartner x hx, ← hpartner y hy, hxy]

/-- A different point with the same projected successor cannot also be periodic. -/
theorem partner_not_mem {α β : Type*} {P : Set α} {T : α → β}
    (hT : Set.InjOn T P) {x y : α} (hx : x ∈ P)
    (hxy : x ≠ y) (ht : T x = T y) : y ∉ P := by
  intro hy
  exact hxy (hT hx hy ht)

/-- Constancy on blocks and periodic injectivity allow at most one point per block. -/
theorem block_injOn {α β γ : Type*} {P : Set α} {T : α → β} {block : α → γ}
    (hT : Set.InjOn T P)
    (hblock : ∀ x y, block x = block y → T x = T y) :
    Set.InjOn block P := by
  intro x hx y hy hxy
  exact hT hx hy (hblock x y hxy)

/-- An embedded component obtains projected injectivity from its actual permutation. -/
theorem component_target_injective {ι α : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i)) :
    Function.Injective (fun i => T (embed i)) := by
  intro i j hij
  apply σ.injective
  apply hembed
  simpa only [hstep] using hij

theorem component_partner_injective {ι α β : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (R : β → α) (partner : ι → β)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    (hpartner : ∀ i, R (partner i) = T (embed i)) :
    Function.Injective partner := by
  intro i j hij
  apply component_target_injective embed σ T hembed hstep
  change T (embed i) = T (embed j)
  rw [← hpartner i, ← hpartner j, hij]

theorem component_partner_not_in_range {ι α : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    {i : ι} {y : α} (hneq : y ≠ embed i)
    (hsame : T y = T (embed i)) : y ∉ Set.range embed := by
  rintro ⟨j, rfl⟩
  have hji := component_target_injective embed σ T hembed hstep hsame
  exact hneq (congrArg embed hji)

theorem component_block_injective {ι α β : Type*}
    (embed : ι → α) (σ : Equiv.Perm ι) (T : α → α) (block : α → β)
    (hembed : Function.Injective embed)
    (hstep : ∀ i, T (embed i) = embed (σ i))
    (hblock : ∀ x y, block x = block y → T x = T y) :
    Function.Injective (fun i => block (embed i)) := by
  intro i j hij
  exact component_target_injective embed σ T hembed hstep
    (hblock (embed i) (embed j) hij)

theorem sum_adjacent_gaps (z : ℕ → ℝ) {g i : ℕ} (hgi : g ≤ i) :
    ∑ j ∈ Finset.Ico g i, (z (j + 1) - z j) = z i - z g := by
  rw [Finset.sum_Ico_eq_sub _ hgi, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

/-- A long normalized source gap supplies a large adjacent selected gap. -/
theorem adjacent_gap_of_mass (z : ℕ → ℝ) {a g i : ℕ} {τ : ℝ}
    (hag : a ≤ g) (hgi : g < i) (hτ : 0 ≤ τ)
    (hgap : τ * (i - a : ℕ) < z i - z g) :
    ∃ j, g ≤ j ∧ j < i ∧ τ < z (j + 1) - z j := by
  by_contra hn
  push Not at hn
  have hs : (∑ j ∈ Finset.Ico g i, (z (j + 1) - z j)) ≤
      ∑ _j ∈ Finset.Ico g i, τ := by
    apply Finset.sum_le_sum
    intro j hj
    exact hn j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
  rw [sum_adjacent_gaps z hgi.le] at hs
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hs
  have hd : (i - g : ℕ) ≤ i - a := by omega
  have hdc : ((i - g : ℕ) : ℝ) ≤ (i - a : ℕ) := by exact_mod_cast hd
  have hm := mul_le_mul_of_nonneg_right hdc hτ
  nlinarith

theorem adjacent_gap_of_ratio (z : ℕ → ℝ) {a g i : ℕ} {τ : ℝ}
    (hag : a ≤ g) (hgi : g < i) (hτ : 0 ≤ τ)
    (hgap : τ < (z i - z g) / (i - a : ℕ)) :
    ∃ j, g ≤ j ∧ j < i ∧ τ < z (j + 1) - z j := by
  have hd : 0 < ((i - a : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < i - a by omega)
  exact adjacent_gap_of_mass z hag hgi hτ ((lt_div_iff₀ hd).mp hgap)

end Problems.Juggler.QuarticProjection
