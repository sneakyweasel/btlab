import Problems.Juggler.FirstPassage
import Problems.Juggler.Defect
import Problems.Juggler.Collapse

namespace Problems.Juggler

/-!
# Descent certificates

One inductive type. The old standalone predicates `Descent` and
`Capture` do not survive. Capture is the `ReachesOne` case.
This file does not claim that every start has a certificate.
-/

inductive DescentCertificate (n : ℕ) : Prop where
  | exponent (w : List Branch) (hw : follows n w) (hgap : exponentGap w)
      (hn : 2 ≤ n)
  | compensated (w : List Branch) (D : ℕ) (hw : follows n w) (hn : 2 ≤ n)
      (hD : D ≤ powerDeficit (floorPower^[w.length] n) n w.length (oddCount w))
      (hgap : n ^ (3 ^ oddCount w) - n ^ (2 ^ w.length) < D)
  | capture (w : List Branch) (hw : follows n w) (himg : image n w = 1)
  | imageLt (w : List Branch) (hw : follows n w) (hlt : image n w < n)

theorem descentCertificate_stop_or_reachesOne {n : ℕ}
    (C : DescentCertificate n) :
    HasFiniteStop n ∨ ReachesOne n := by
  cases C with
  | exponent w hw hgap hn =>
      have hlt := power_bound_contracts hn hw hgap
      refine Or.inl ⟨w.length, ?_, hlt⟩
      cases w with
      | nil =>
          simp [exponentGap] at hgap
      | cons _ rest =>
          exact Nat.succ_pos rest.length
  | compensated w D hw hn hD hgap =>
      have hlt := power_bound_compensated_contracts_follows hn hw hD hgap
      refine Or.inl ⟨w.length, ?_, hlt⟩
      have : floorPower^[w.length] n < n := hlt
      exact Nat.pos_of_ne_zero fun h0 => by
        have : n ≤ floorPower^[0] n := by simp
        rw [← h0] at this
        omega
  | capture w hw himg =>
      exact Or.inr ⟨w.length, by rw [← image_eq_iterate, himg]⟩
  | imageLt w hw hlt =>
      refine Or.inl ⟨w.length, ?_, by simpa [image_eq_iterate] using hlt⟩
      have : image n w < n := hlt
      exact Nat.pos_of_ne_zero fun h0 => by
        have himg : image n w = n := by
          rw [image_eq_iterate, h0, Function.iterate_zero_apply]
        omega

theorem descentCertificate_of_coeffStop {n : ℕ} (hn : 2 ≤ n)
    (h : HasFiniteCoeffStop n) : DescentCertificate n := by
  obtain ⟨k, hk, hgap⟩ := h
  refine DescentCertificate.exponent (word n k) (follows_word_self n k) ?_ hn
  unfold exponentGap
  simpa [word_length] using trajectoryExponentGap_iff.mp hgap

theorem capture_reachesOne {n : ℕ} {w : List Branch}
    (_hw : follows n w) (himg : image n w = 1) : ReachesOne n :=
  ⟨w.length, by rw [← image_eq_iterate, himg]⟩

/-- Certified basin `{1}`. Naming alias of `s = 1`, not a second attractor. -/
def InertBasin (s : ℕ) : Prop :=
  s = 1

theorem capture_of_suffix {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows (image n u) v)
    (himg : image (image n u) v = 1) :
    follows n (u ++ v) ∧ image n (u ++ v) = 1 :=
  ⟨follows_append hu hv, by rw [image_append, himg]⟩

theorem capture_append {n : ℕ} {u v : List Branch}
    (hu : follows n u ∧ image n u = 1)
    (hv : follows (image n u) v ∧ image (image n u) v = 1) :
    follows n (u ++ v) ∧ image n (u ++ v) = 1 :=
  capture_of_suffix hu.1 hv.1 hv.2

theorem even_tower_capture {k : ℕ} (hk : 1 ≤ k) :
    follows (2 ^ (2 ^ (k - 1))) (List.replicate k Branch.even) ∧
      image (2 ^ (2 ^ (k - 1))) (List.replicate k Branch.even) = 1 :=
  even_tower_to_one hk

theorem even_tower_odd_tail_capture {k o : ℕ} (hk : 1 ≤ k) :
    follows (2 ^ (2 ^ (k - 1)))
        (List.replicate k Branch.even ++ List.replicate o Branch.odd) ∧
      image (2 ^ (2 ^ (k - 1)))
          (List.replicate k Branch.even ++ List.replicate o Branch.odd) = 1 :=
  ⟨(even_tower_odd_tail_contracts (k := k) (o := o) hk).1,
    (even_tower_odd_tail_contracts (k := k) (o := o) hk).2.1⟩

theorem odd_even_tower_seven_capture :
    follows 7 wordOEEE9 ∧ image 7 wordOEEE9 = 1 :=
  ⟨odd_even_tower_seven.1, odd_even_tower_seven.2.1⟩

theorem nested_even_collapse_2500_capture :
    follows 2500 wordEE_OEEE12 ∧ image 2500 wordEE_OEEE12 = 1 :=
  ⟨nested_even_collapse_2500.1, nested_even_collapse_2500.2.1⟩

theorem first_even_cell_capture {n : ℕ} {v : List Branch}
    (hw : follows n (.even :: v)) (hcap : image n.sqrt v = 1) :
    follows n (.even :: v) ∧ image n (.even :: v) = 1 :=
  ⟨hw, by
    have : image n (.even :: v) = image n.sqrt v := by
      rw [image_eq_iterate, image_eq_iterate, List.length_cons, iterate_cons]
      have heven : n % 2 = 0 := hw.1
      simp [floorPower_even_eq heven]
    rw [this, hcap]⟩

theorem descent_of_below {n : ℕ} {w : List Branch}
    (hbelow : ∀ m, m < n → ReachesOne m)
    (_hw : follows n w) (hlt : image n w < n) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm (hbelow _ hlt)

theorem minimal_avoids_progress {n : ℕ} {w : List Branch}
    (hfail : ¬ReachesOne n) (hmin : ∀ m, m < n → ReachesOne m) :
    ¬(follows n w ∧ image n w < n) ∧ ¬(follows n w ∧ image n w = 1) :=
  ⟨fun hd => hfail (descent_of_below hmin hd.1 hd.2),
    fun hc => hfail (capture_reachesOne hc.1 hc.2)⟩

theorem even_word_descent {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hw : follows n (List.replicate k Branch.even)) :
    follows n (List.replicate k Branch.even) ∧
      image n (List.replicate k Branch.even) < n :=
  ⟨hw, by
    have himg := image_eq_iterate n (List.replicate k Branch.even)
    rw [himg, List.length_replicate]
    exact even_word_contracts hn hk hw⟩

theorem minimal_odd_start {n : ℕ} (hn : 3 ≤ n)
    (hfail : ¬ReachesOne n) (hmin : ∀ m, m < n → ReachesOne m) :
    n % 2 = 1 := by
  by_cases heven : n % 2 = 0
  · have hw : follows n (List.replicate 1 Branch.even) := ⟨heven, trivial⟩
    have hd := even_word_descent (by omega) (by decide) hw
    exact (minimal_avoids_progress (w := List.replicate 1 Branch.even)
      hfail hmin).1 hd |>.elim
  · omega

theorem minimal_avoids_reachesOne_image {n : ℕ} {w : List Branch}
    (hfail : ¬ReachesOne n) : ¬ReachesOne (image n w) :=
  fun hm => hfail (reachesOne_of_image hm)

end Problems.Juggler
