import Problems.Juggler.CubicBand
import Problems.Juggler.CubicRotation

namespace Problems.Juggler

/-- Exact injective conjugacy preserves all iterates. -/
theorem cubic_conjugacy_iterate {α β : Type*} (c : α → β) (p : α → α)
    (f : β → β) (hstep : ∀ i, c (p i) = f (c i)) (k : ℕ) (i : α) :
    c (p^[k] i) = f^[k] (c i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]

/-- Least periods transfer from the sorted rank permutation to actual states. -/
theorem cubic_conjugacy_minimalPeriod {α β : Type*} (c : α → β)
    (hc : Function.Injective c) (p : α → α) (f : β → β)
    (hstep : ∀ i, c (p i) = f (c i)) (i : α) :
    Function.minimalPeriod p i = Function.minimalPeriod f (c i) := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  change p^[k] i = i ↔ f^[k] (c i) = c i
  rw [← cubic_conjugacy_iterate c p f hstep]
  exact hc.eq_iff.symm

/-- One threshold has one least period on its entire periodic set. -/
theorem threshold_periods_equal {b x y : ℕ} (hb : 3 ≤ b)
    (hx : x ∈ thresholdPeriodicStates b) (hy : y ∈ thresholdPeriodicStates b) :
    Function.minimalPeriod (thresholdMap b) x =
      Function.minimalPeriod (thresholdMap b) y := by
  classical
  let s := thresholdPeriodicStates b
  let c := s.orderEmbOfFin rfl
  let q := s.orderIsoOfFin rfl
  obtain ⟨p, o, _, hstep, _, hrot⟩ := threshold_all_periodic_rank_rotation hb
  let ix := q.symm ⟨x, hx⟩
  let iy := q.symm ⟨y, hy⟩
  have hxi : c ix = x := by
    change (q (q.symm ⟨x, hx⟩)).val = x
    rw [q.apply_symm_apply]
  have hyi : c iy = y := by
    change (q (q.symm ⟨y, hy⟩)).val = y
    rw [q.apply_symm_apply]
  rw [← hxi, ← hyi,
    ← cubic_conjugacy_minimalPeriod c c.injective p (thresholdMap b) hstep,
    ← cubic_conjugacy_minimalPeriod c c.injective p (thresholdMap b) hstep,
    rankRotation_minimalPeriod p hrot, rankRotation_minimalPeriod p hrot]

/-- A primitive cubic-band orbit has the exact ceiling-mechanical odd prefixes. -/
theorem cubicBand_mechanical_itinerary {m L : ℕ} (hL : 0 < L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hstep : ∀ i, c (p i) = floorPower (c i))
    (hcycle : p.IsCycleOn (↑(Finset.univ : Finset (Fin L)))) :
    ∃ o ≤ L, Nat.Coprime L o ∧
      (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L) ∧
      ∀ k, (∑ j ∈ Finset.range k,
        if floorPower^[j] (c ⟨0, hL⟩) % 2 = 1 then 1 else 0) =
          (k * o + L - 1) / L := by
  classical
  obtain ⟨o, ho, hcut, hcard, hrot⟩ := cubicBand_sorted_rotation c hc p hband hstep
  refine ⟨o, ho, (Nat.coprime_self_sub_right ho).mp
    (rankRotation_coprime hL p hrot hcycle), hcard, hrot, ?_⟩
  intro k
  have hconj := cubic_conjugacy_iterate c p floorPower hstep
  simp_rw [← hconj, hcut]
  exact rankRotation_mechanical_prefix hL (Nat.add_sub_of_le ho) p hrot k

end Problems.Juggler
