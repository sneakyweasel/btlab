import Problems.Juggler.Dynamics
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace Problems.Juggler

/-- The finite half-open cubic band. -/
def InCubicBand (b x : ℕ) : Prop := b ≤ x ∧ x < b ^ 3

/-- A parity-relaxed map: its branch is chosen by size. -/
def thresholdMap (b x : ℕ) : ℕ :=
  if x < b ^ 2 then (x ^ 3).sqrt else x.sqrt

theorem thresholdMap_lower_gt {b x : ℕ} (hb : 3 ≤ b)
    (hx : b ≤ x) (hlo : x < b ^ 2) : x < thresholdMap b x := by
  rw [thresholdMap, if_pos hlo]
  have hh := Nat.le_sqrt.mpr (show (x + 1) * (x + 1) ≤ x ^ 3 by
    simpa [pow_two] using succ_sq_le_cube (hb.trans hx))
  omega

theorem thresholdMap_upper_lt {b x : ℕ} (hb : 3 ≤ b)
    (hx : b ≤ x) (hhi : b ^ 2 ≤ x) : thresholdMap b x < x := by
  rw [thresholdMap, if_neg (by omega)]
  exact Nat.sqrt_lt_self (by omega)

theorem thresholdMap_invariant {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) : InCubicBand b (thresholdMap b x) := by
  rcases hx with ⟨hbx, hxc⟩
  by_cases hlo : x < b ^ 2
  · refine ⟨hbx.trans (Nat.le_of_lt (thresholdMap_lower_gt hb hbx hlo)), ?_⟩
    rw [thresholdMap, if_pos hlo, Nat.sqrt_lt]
    have hh := Nat.pow_lt_pow_left hlo (by decide : 3 ≠ 0)
    nlinarith [show (b ^ 2) ^ 3 = b ^ 3 * b ^ 3 by ring]
  · rw [thresholdMap, if_neg hlo]
    refine ⟨Nat.le_sqrt.mpr (by simpa [pow_two] using Nat.le_of_not_gt hlo), ?_⟩
    exact (Nat.sqrt_le_self x).trans_lt hxc

theorem thresholdMap_ne_self {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) : thresholdMap b x ≠ x := by
  by_cases hlo : x < b ^ 2
  · exact (thresholdMap_lower_gt hb hx.1 hlo).ne'
  · exact (thresholdMap_upper_lt hb hx.1 (by omega)).ne

/-- Closure in a cubic band forces the actual parity at the square seam. -/
theorem cubicBand_parity_iff {m x : ℕ}
    (hx : InCubicBand m x) (hj : InCubicBand m (floorPower x)) :
    x % 2 = 1 ↔ x < m ^ 2 := by
  rcases hx with ⟨_, _⟩
  constructor
  · intro ho
    by_contra h
    have hh : m ^ 3 ≤ floorPower x := by
      rw [floorPower_odd_eq ho]
      apply Nat.le_sqrt.mpr
      have hp := Nat.pow_le_pow_left (Nat.le_of_not_gt h) 3
      nlinarith [show (m ^ 2) ^ 3 = m ^ 3 * m ^ 3 by ring]
    exact (not_lt_of_ge hh) hj.2
  · intro hlo
    rcases Nat.mod_two_eq_zero_or_one x with he | ho
    · have hroot : floorPower x < m := by
        rw [floorPower_even_eq he, Nat.sqrt_lt]
        simpa [pow_two] using hlo
      exact False.elim ((not_lt_of_ge hj.1) hroot)
    · exact ho

theorem cubicBand_floorPower_eq_threshold {m x : ℕ}
    (hx : InCubicBand m x) (hj : InCubicBand m (floorPower x)) :
    floorPower x = thresholdMap m x := by
  have hpar := cubicBand_parity_iff hx hj
  by_cases hlo : x < m ^ 2
  · rw [thresholdMap, if_pos hlo, floorPower_odd_eq (hpar.mpr hlo)]
  · have he : x % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · exact h
      · exact False.elim (hlo (hpar.mp h))
    rw [thresholdMap, if_neg hlo, floorPower_even_eq he]

/-- Weak branch-image separation; injectivity on periodic points removes ties. -/
theorem thresholdMap_image_separation {b x y : ℕ}
    (hx : InCubicBand b x) (hy : InCubicBand b y)
    (hhi : b ^ 2 ≤ x) (hlo : y < b ^ 2) :
    thresholdMap b x ≤ thresholdMap b y := by
  rw [thresholdMap, if_neg (by omega), thresholdMap, if_pos hlo]
  exact Nat.sqrt_le_sqrt ((Nat.le_of_lt hx.2).trans
    (Nat.pow_le_pow_left hy.1 3))

/-- Reindexing two increasing blocks with separated images forces rotation. -/
theorem twoBlock_rank_rotation {L o : ℕ} (ho : o ≤ L)
    (p : Fin L → Fin L)
    (hlo : ∀ i j, i < j → j.val < o → p i < p j)
    (hhi : ∀ i j, i < j → o ≤ i.val → p i < p j)
    (hsep : ∀ i j, o ≤ i.val → j.val < o → p i < p j)
    (i : Fin L) :
    (p i).val = if i.val < o then i.val + (L - o) else i.val - o := by
  let q : Fin L → Fin L := fun j =>
    if h : j.val < L - o then ⟨j.val + o, by omega⟩
    else ⟨j.val - (L - o), by omega⟩
  have hmono : StrictMono (p ∘ q) := by
    intro a b hab
    dsimp [q]
    split_ifs with ha hb hb
    · apply hhi <;> simp only [Fin.lt_def] at * <;> omega
    · apply hsep <;> simp only <;> omega
    · simp only [Fin.lt_def] at hab
      omega
    · apply hlo <;> simp only [Fin.lt_def] at * <;> omega
  have hident : ∀ j, p (q j) = j := fun _ => hmono.apply_eq
  by_cases hi : i.val < o
  · let j : Fin L := ⟨i.val + (L - o), by omega⟩
    have hq : q j = i := by
      dsimp [q, j]
      rw [dif_neg (by omega)]
      apply Fin.ext
      simp only
      omega
    have hj := congrArg Fin.val (hident j)
    simpa [Function.comp_apply, hq, j, hi] using hj
  · let j : Fin L := ⟨i.val - o, by omega⟩
    have hq : q j = i := by
      dsimp [q, j]
      rw [dif_pos (by omega)]
      apply Fin.ext
      simp only
      omega
    have hj := congrArg Fin.val (hident j)
    simpa [Function.comp_apply, hq, j, hi] using hj

theorem twoBlock_rank_rotation_mod {L o : ℕ} (ho : o ≤ L)
    (p : Fin L → Fin L)
    (hlo : ∀ i j, i < j → j.val < o → p i < p j)
    (hhi : ∀ i j, i < j → o ≤ i.val → p i < p j)
    (hsep : ∀ i j, o ≤ i.val → j.val < o → p i < p j)
    (i : Fin L) : (p i).val = (i.val + (L - o)) % L := by
  rw [twoBlock_rank_rotation ho p hlo hhi hsep]
  split_ifs with hi
  · exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The order theorem applies to any sorted invariant permutation of the threshold map. -/
theorem threshold_rank_rotation {b L o : ℕ} (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = thresholdMap b (c i)) (i : Fin L) :
    (p i).val = (i.val + (L - o)) % L := by
  apply twoBlock_rank_rotation_mod ho p
  · intro a d had hd
    apply hc.lt_iff_lt.mp
    have ha : c a < b ^ 2 := (hcut a).mpr (by exact lt_trans had hd)
    have hd' := (hcut d).mpr hd
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep, thresholdMap, if_pos ha, thresholdMap, if_pos hd']
      exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left (hc.monotone (le_of_lt had)) 3)
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt had) (p.injective (hc.injective he)))
  · intro a d had ha
    apply hc.lt_iff_lt.mp
    have ha' : ¬ c a < b ^ 2 := fun h => by have := (hcut a).mp h; omega
    have hd' : ¬ c d < b ^ 2 := fun h => by have := (hcut d).mp h; omega
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep, thresholdMap, if_neg ha', thresholdMap, if_neg hd']
      exact Nat.sqrt_le_sqrt (hc.monotone (le_of_lt had))
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt had) (p.injective (hc.injective he)))
  · intro a d ha hd
    apply hc.lt_iff_lt.mp
    have ha' : b ^ 2 ≤ c a := by
      by_contra h
      have := (hcut a).mp (by omega)
      omega
    have hd' := (hcut d).mpr hd
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep]
      exact thresholdMap_image_separation (hband a) (hband d) ha' hd'
    apply lt_of_le_of_ne hle
    intro he
    have hh := p.injective (hc.injective he)
    have := congrArg Fin.val hh
    omega

theorem cubicBand_rank_rotation {m L o : ℕ} (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hcut : ∀ i, c i < m ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = floorPower (c i)) (i : Fin L) :
    (p i).val = (i.val + (L - o)) % L := by
  apply threshold_rank_rotation ho c hc p hband hcut
  intro j
  rw [hstep]
  apply cubicBand_floorPower_eq_threshold (hband j)
  rw [← hstep]
  exact hband (p j)

/-- Every finite self-map has a periodic state. -/
theorem finite_map_periodic_state {α : Type*} [Finite α] (f : α → α) (a : α) :
    ∃ x k, 0 < k ∧ f^[k] x = x := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] a)
  have aux : ∀ i j : ℕ, i < j → f^[i] a = f^[j] a →
      ∃ x k, 0 < k ∧ f^[k] x = x := by
    intro u v huv huv'
    refine ⟨f^[u] a, v - u, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    exact huv'.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact aux i j h heq
  · exact aux j i h heq.symm

/-- At every threshold at least three there is a nontrivial periodic state in the band. -/
theorem thresholdMap_has_nontrivial_periodic_state {b : ℕ} (hb : 3 ≤ b) :
    ∃ x k, InCubicBand b x ∧ 2 ≤ k ∧ (thresholdMap b)^[k] x = x := by
  let α := {x : Fin (b ^ 3) // b ≤ x.val}
  have hbb : b < b ^ 3 := by nlinarith [sq_nonneg (b - 1 : ℤ)]
  let a : α := ⟨⟨b, hbb⟩, le_rfl⟩
  let f : α → α := fun x =>
    let h := thresholdMap_invariant hb ⟨x.property, x.val.isLt⟩
    ⟨⟨thresholdMap b x.val.val, h.2⟩, h.1⟩
  obtain ⟨x, k, hk, hperiod⟩ := finite_map_periodic_state f a
  have hiter : ∀ n (z : α), (f^[n] z).val.val = (thresholdMap b)^[n] z.val.val := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
  have hp : (thresholdMap b)^[k] x.val.val = x.val.val := by
    rw [← hiter, hperiod]
  refine ⟨x.val.val, k, ⟨x.property, x.val.isLt⟩, ?_, hp⟩
  by_contra h
  have hk1 : k = 1 := by omega
  rw [hk1, Function.iterate_one] at hp
  exact thresholdMap_ne_self hb ⟨x.property, x.val.isLt⟩ hp

/-- A threshold in a sorted finite list selects exactly an initial segment. -/
theorem sorted_threshold_cut {L t : ℕ} (c : Fin L → ℕ) (hc : StrictMono c) :
    ∃ o ≤ L, (∀ i, c i < t ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => c i < t)).card = o := by
  classical
  let s := Finset.univ.filter (fun i => t ≤ c i)
  by_cases hs : s.Nonempty
  · let j := s.min' hs
    have hj : t ≤ c j := (Finset.mem_filter.mp (s.min'_mem hs)).2
    have hcut : ∀ i, c i < t ↔ i.val < j.val := by
      intro i
      constructor
      · intro hi
        by_contra h
        have hji : j ≤ i := by omega
        have hle := hc.monotone hji
        omega
      · intro hi
        by_contra h
        have himem : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hle : j ≤ i := s.min'_le _ himem
        omega
    refine ⟨j.val, Nat.le_of_lt j.isLt, hcut, ?_⟩
    have heq : Finset.univ.filter (fun i => c i < t) = Finset.Iio j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      exact hcut i
    rw [heq, Fin.card_Iio]
  · have hcut : ∀ i, c i < t := by
      intro i
      by_contra h
      apply hs
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    refine ⟨L, le_rfl, fun i => iff_of_true (hcut i) i.isLt, ?_⟩
    simp [hcut]

/-- Rotation follows from closure alone after sorting; the cutoff is the branch count. -/
theorem threshold_sorted_rotation {b L : ℕ}
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hstep : ∀ i, c (p i) = thresholdMap b (c i)) :
    ∃ o ≤ L, (∀ i, c i < b ^ 2 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => c i < b ^ 2)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L) := by
  obtain ⟨o, ho, hcut, hcard⟩ := sorted_threshold_cut c hc (t := b ^ 2)
  exact ⟨o, ho, hcut, hcard, threshold_rank_rotation ho c hc p hband hcut hstep⟩

/-- The actual odd count is the cutoff for a sorted cubic-band invariant permutation. -/
theorem cubicBand_sorted_rotation {m L : ℕ}
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (p i) = floorPower (c i)) :
    ∃ o ≤ L, (∀ i, c i % 2 = 1 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L) := by
  obtain ⟨o, ho, hcut, hcard⟩ := sorted_threshold_cut c hc (t := m ^ 2)
  have hpar : ∀ i, c i % 2 = 1 ↔ c i < m ^ 2 := by
    intro i
    apply cubicBand_parity_iff (hband i)
    rw [← hstep]
    exact hband (p i)
  refine ⟨o, ho, fun i => (hpar i).trans (hcut i), ?_,
    cubicBand_rank_rotation ho c hc p hband hcut hstep⟩
  simpa only [hpar] using hcard

/-- Any finite invariant injection has an induced permutation in sorted ranks. -/
theorem sorted_invariant_permutation (s : Finset ℕ) (f : ℕ → ℕ)
    (hclosed : ∀ x ∈ s, f x ∈ s) (hinj : Set.InjOn f s) :
    ∃ p : Equiv.Perm (Fin s.card), ∀ i,
      s.orderEmbOfFin rfl (p i) = f (s.orderEmbOfFin rfl i) := by
  classical
  let e := s.orderIsoOfFin rfl
  let g : s → s := fun x => ⟨f x, hclosed x x.property⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact hinj x.property y.property (congrArg Subtype.val h)
  let q := Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩
  let p : Equiv.Perm (Fin s.card) := (e.toEquiv.trans q).trans e.toEquiv.symm
  refine ⟨p, ?_⟩
  intro i
  change ((e (e.symm (q (e i)))) : ℕ) = f ((e i) : ℕ)
  rw [e.apply_symm_apply]
  rfl

/-- Periodic points supply injectivity without any global injectivity assumption. -/
theorem periodicPoints_injOn (f : ℕ → ℕ) :
    Set.InjOn f (Function.periodicPts f) := by
  intro x hx y hy heq
  rcases hx with ⟨k, hk, hx⟩
  rcases hy with ⟨l, hl, hy⟩
  exact hx.eq_of_apply_eq hy hk hl heq

/-- The complete periodic set inside the threshold band. -/
noncomputable def thresholdPeriodicStates (b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico b (b ^ 3)).filter (fun x => x ∈ Function.periodicPts (thresholdMap b))

theorem mem_thresholdPeriodicStates {b x : ℕ} :
    x ∈ thresholdPeriodicStates b ↔
      InCubicBand b x ∧ x ∈ Function.periodicPts (thresholdMap b) := by
  classical
  simp [thresholdPeriodicStates, InCubicBand]

theorem thresholdPeriodicStates_nonempty {b : ℕ} (hb : 3 ≤ b) :
    (thresholdPeriodicStates b).Nonempty := by
  obtain ⟨x, k, hx, hk, hp⟩ := thresholdMap_has_nontrivial_periodic_state hb
  exact ⟨x, mem_thresholdPeriodicStates.mpr
    ⟨hx, ⟨k, by omega, hp⟩⟩⟩

theorem thresholdPeriodicStates_closed {b : ℕ} (hb : 3 ≤ b) :
    ∀ x ∈ thresholdPeriodicStates b, thresholdMap b x ∈ thresholdPeriodicStates b := by
  intro x hx
  rcases mem_thresholdPeriodicStates.mp hx with ⟨hband, k, hk, hp⟩
  exact mem_thresholdPeriodicStates.mpr
    ⟨thresholdMap_invariant hb hband, ⟨k, hk, hp.apply⟩⟩

/-- Sorting all periodic points gives one rank translation, even when several cycles occur. -/
theorem threshold_all_periodic_rank_rotation {b : ℕ} (hb : 3 ≤ b) :
    let s := thresholdPeriodicStates b
    ∃ (p : Equiv.Perm (Fin s.card)) (o : ℕ), o ≤ s.card ∧
      (∀ i, s.orderEmbOfFin rfl (p i) = thresholdMap b (s.orderEmbOfFin rfl i)) ∧
      (∀ i, s.orderEmbOfFin rfl i < b ^ 2 ↔ i.val < o) ∧
      (∀ i, (p i).val = (i.val + (s.card - o)) % s.card) := by
  classical
  let s := thresholdPeriodicStates b
  have hinj : Set.InjOn (thresholdMap b) s := by
    intro x hx y hy heq
    exact periodicPoints_injOn (thresholdMap b)
      (mem_thresholdPeriodicStates.mp hx).2 (mem_thresholdPeriodicStates.mp hy).2 heq
  obtain ⟨p, hstep⟩ := sorted_invariant_permutation s (thresholdMap b)
    (thresholdPeriodicStates_closed hb) hinj
  have hband : ∀ i, InCubicBand b (s.orderEmbOfFin rfl i) := fun i =>
    (mem_thresholdPeriodicStates.mp (s.orderEmbOfFin_mem rfl i)).1
  obtain ⟨o, ho, hcut, _, hrot⟩ := threshold_sorted_rotation
    (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl).strictMono p hband hstep
  exact ⟨p, o, ho, hstep, hcut, hrot⟩

/-- A conjugated single orbit remains a single cycle of the rank permutation. -/
theorem rank_isCycleOn_of_connected {L : ℕ} (c : Fin L → ℕ)
    (hc : Function.Injective c) (p : Equiv.Perm (Fin L)) (f : ℕ → ℕ)
    (hstep : ∀ i, c (p i) = f (c i))
    (hconnected : ∀ i j, ∃ k : ℕ, f^[k] (c i) = c j) :
    p.IsCycleOn Set.univ := by
  refine ⟨p.bijective.bijOn_univ, ?_⟩
  intro i _ j _
  obtain ⟨k, hk⟩ := hconnected i j
  have hsemi : Function.Semiconj c p f := hstep
  have heq : (p ^ k) i = j := by
    apply hc
    rw [Equiv.Perm.coe_pow, (hsemi.iterate_right k).eq, hk]
  exact ⟨(k : ℤ), by simpa using heq⟩

/-- At a state in the band, equality with Juggler is exactly parity compatibility. -/
theorem thresholdMap_eq_floorPower_iff {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x) :
    thresholdMap b x = floorPower x ↔ (x % 2 = 1 ↔ x < b ^ 2) := by
  have hroots : x.sqrt < (x ^ 3).sqrt := by
    have hlarge : x < (x ^ 3).sqrt := by
      have hh := Nat.le_sqrt.mpr (show (x + 1) * (x + 1) ≤ x ^ 3 by
        simpa [pow_two] using succ_sq_le_cube (hb.trans hx.1))
      omega
    exact (Nat.sqrt_le_self x).trans_lt hlarge
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · rw [floorPower_even_eq he]
    by_cases hlo : x < b ^ 2
    · simp [thresholdMap, hlo, he, ne_of_gt hroots]
    · simp [thresholdMap, hlo, he]
  · rw [floorPower_odd_eq ho]
    by_cases hlo : x < b ^ 2
    · simp [thresholdMap, hlo, ho]
    · simp [thresholdMap, hlo, ho, ne_of_lt hroots]

/-- Exact compatibility along a threshold orbit identifies its iterates with Juggler. -/
theorem threshold_iterates_eq_of_compatible {b x : ℕ} (hb : 3 ≤ b)
    (hx : InCubicBand b x)
    (hcompatible : ∀ k, ((thresholdMap b)^[k] x) % 2 = 1 ↔
      (thresholdMap b)^[k] x < b ^ 2) :
    ∀ k, (thresholdMap b)^[k] x = floorPower^[k] x := by
  have hband : ∀ k, InCubicBand b ((thresholdMap b)^[k] x) := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact thresholdMap_invariant hb ih
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      (thresholdMap_eq_floorPower_iff hb (hband k)).mpr (hcompatible k), ih]

/-- The existence assertion can be stated with a primitive period and distinct pre-return states. -/
theorem thresholdMap_exists_primitive {b : ℕ} (hb : 3 ≤ b) :
    ∃ x L, InCubicBand b x ∧ 2 ≤ L ∧ (thresholdMap b)^[L] x = x ∧
      ∀ i j, i < L → j < L →
        (thresholdMap b)^[i] x = (thresholdMap b)^[j] x → i = j := by
  obtain ⟨x, k, hx, hk, hp⟩ := thresholdMap_has_nontrivial_periodic_state hb
  have hper : Function.IsPeriodicPt (thresholdMap b) k x := hp
  have hpos := hper.minimalPeriod_pos (by omega)
  have hne : Function.minimalPeriod (thresholdMap b) x ≠ 1 := by
    intro h
    exact thresholdMap_ne_self hb hx
      (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  refine ⟨x, Function.minimalPeriod (thresholdMap b) x, hx, by omega,
    Function.isPeriodicPt_minimalPeriod _ _, ?_⟩
  intro i j hi hj heq
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp heq

/-- A nonempty invariant threshold permutation uses both branches. -/
theorem threshold_branch_count_bounds {b L o : ℕ} (hb : 3 ≤ b) (hL : 0 < L)
    (ho : o ≤ L) (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand b (c i))
    (hcut : ∀ i, c i < b ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = thresholdMap b (c i)) : 0 < o ∧ o < L := by
  have hrot := threshold_rank_rotation ho c hc p hband hcut hstep
  let i : Fin L := ⟨0, hL⟩
  have hnot : p i ≠ i := by
    intro h
    exact thresholdMap_ne_self hb (hband i) ((hstep i).symm.trans (congrArg c h))
  have ho0 : o ≠ 0 := by
    intro h
    apply hnot
    apply Fin.ext
    simpa [h, Nat.add_mod, Nat.mod_eq_of_lt i.isLt] using hrot i
  have hoL : o ≠ L := by
    intro h
    apply hnot
    apply Fin.ext
    simpa [h, Nat.mod_eq_of_lt i.isLt] using hrot i
  omega

end Problems.Juggler
