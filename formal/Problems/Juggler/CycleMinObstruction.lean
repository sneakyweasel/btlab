import Problems.Juggler.Preimages
import Problems.Juggler.EvenCountThree

namespace Problems.Juggler

/-!
# CycleMin odd-run cube and second-OO transport

The `OOO` next-square threshold is the `n = 3` inheritance. On a
cycle minimum `n ≥ 12`, the first two odds already sit at
`(n+1)^2`, so one more odd lifts the residual to `(n+1)^3`.

An internal `OO` after the first even event transports the next
residual to `(y+1)^2` with `y > n`. This is not a halt theorem,
not a four-even assembler, and not a last-cluster census.
-/

theorem follows_replicate_odd_of_le {n a k : ℕ} (hk : k ≤ a)
    (hw : follows n (List.replicate a Branch.odd)) :
    follows n (List.replicate k Branch.odd) := by
  have hsplit : List.replicate a Branch.odd =
      List.replicate k Branch.odd ++ List.replicate (a - k) Branch.odd := by
    have hsum : k + (a - k) = a := Nat.add_sub_of_le hk
    rw [← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - k) Branch.odd)
    (by simpa [hsplit] using hw)

theorem replicate_odd_three :
    List.replicate 3 Branch.odd = [.odd, .odd, .odd] :=
  rfl

theorem replicate_odd_two :
    List.replicate 2 Branch.odd = [.odd, .odd] :=
  rfl

/-- On a `CycleMin` whose first odd run has length at least three, the
first three-odd residual is at least `(n+1)^3`. -/
theorem cycleMin_ooo_residual_ge_cube {n a : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (ha : 3 ≤ a)
    (h : CycleMin n (oddEvenBlock a 1 ++ v)) :
    (n + 1) ^ 3 ≤ image n (List.replicate 3 Branch.odd) := by
  have hn12 := cycleMin_ge_twelve hn h
  have hn5 : 5 ≤ n := le_trans (by decide : (5 : ℕ) ≤ 12) hn12
  have hw : follows n (oddEvenBlock a 1) := follows_of_append_left h.1.1
  have hodds : follows n (List.replicate a Branch.odd) :=
    follows_of_append_left (v := List.replicate 1 Branch.even) hw
  have h3 : follows n (List.replicate 3 Branch.odd) :=
    follows_replicate_odd_of_le (by omega : (3 : ℕ) ≤ a) hodds
  have hOOO : follows n [.odd, .odd, .odd] := by
    simpa [replicate_odd_three] using h3
  have hcube := ooo_residual_ge_cube hn5 hOOO
  simpa [image_odd_run, replicate_odd_three] using hcube

/-- After the first `O^a E` on a `CycleMin`, an immediate odd run of
length at least two overshoots the landing `y`: the next two-odd
residual is at least `(y+1)^2`. -/
theorem cycleMin_transport_second_oo {n a b : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (_ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : CycleMin n
      (oddEvenBlock a 1 ++ List.replicate b Branch.odd ++ v)) :
    (image n (oddEvenBlock a 1) + 1) ^ 2 ≤
      image (image n (oddEvenBlock a 1)) (List.replicate 2 Branch.odd) := by
  have hassoc :
      oddEvenBlock a 1 ++ List.replicate b Branch.odd ++ v =
        oddEvenBlock a 1 ++ (List.replicate b Branch.odd ++ v) := by
    simp [List.append_assoc]
  have h' : CycleMin n
      (oddEvenBlock a 1 ++ (List.replicate b Branch.odd ++ v)) := by
    simpa [hassoc] using h
  have hover := cycleMin_first_even_overshoots hn h'
  set y := image n (oddEvenBlock a 1)
  have hn12 := cycleMin_ge_twelve hn h
  have hygt : n < y := hover.2
  have hy13 : 13 ≤ y :=
    Nat.succ_le_of_lt (lt_of_le_of_lt hn12 hygt)
  have hy5 : 5 ≤ y := le_trans (by decide : (5 : ℕ) ≤ 13) hy13
  have htail : follows y (List.replicate b Branch.odd ++ v) :=
    follows_of_append_right (u := oddEvenBlock a 1)
      (by simpa [hassoc] using h.1.1)
  have hodds : follows y (List.replicate b Branch.odd) :=
    follows_of_append_left htail
  have h2 : follows y (List.replicate 2 Branch.odd) :=
    follows_replicate_odd_of_le (by omega : (2 : ℕ) ≤ b) hodds
  have hOO : follows y [.odd, .odd] := by
    simpa [replicate_odd_two] using h2
  have hth := oo_suffix_threshold hy5 hOO
  simpa [image_odd_run, replicate_odd_two] using hth

/-- The transported second residual sits at least one extra integer
above the first-even cell. -/
theorem cycleMin_transport_second_oo_ge {n a b : ℕ} {v : List Branch}
    (hn : 2 ≤ n) (_ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : CycleMin n
      (oddEvenBlock a 1 ++ List.replicate b Branch.odd ++ v)) :
    (n + 2) ^ 2 ≤
      image (image n (oddEvenBlock a 1)) (List.replicate 2 Branch.odd) := by
  have hth := cycleMin_transport_second_oo hn _ha hb h
  have h' : CycleMin n
      (oddEvenBlock a 1 ++ (List.replicate b Branch.odd ++ v)) := by
    simpa [List.append_assoc] using h
  have hygt : n < image n (oddEvenBlock a 1) :=
    (cycleMin_first_even_overshoots hn h').2
  have hy1 : n + 1 ≤ image n (oddEvenBlock a 1) := Nat.succ_le_of_lt hygt
  have hbound :
      (n + 2) ^ 2 ≤ (image n (oddEvenBlock a 1) + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hy1) 2
  exact le_trans hbound hth

end Problems.Juggler
