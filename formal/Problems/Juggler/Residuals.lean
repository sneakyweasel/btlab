import Problems.Juggler.DefectLowerBound
import Problems.Juggler.MinimumRelative
import Problems.Juggler.Minimal
import Problems.Juggler.Scale

namespace Problems.Juggler

/-!
# First even residual and post-overshoot residual of an odd-to-odd start

An even residual `z` falls into one of three square cells relative to
an odd `n`: below `n^2`, the return cell `n^2 < z < (n+1)^2`, or
overshoot `(n+1)^2 ≤ z`. Under `MinimalNonTerm`, the first cell is
impossible and the first `O^a E` block is neither an image descent
`T_w(n) < n` nor a capture `T_w(n) = 1`. The leftover is a
return-to-start cycle candidate or strict overshoot.

A strict overshoot produces a later state `y = T(z) > n`. That `y` may
be even or odd. `ReturnBelow` is a finite-prefix certificate, distinct
from an image descent at the residual state. A later return below the
original start is `FiniteProgress` at `n`, and is impossible on a
`MinimalNonTerm` trajectory. An even post-even residual on a CE forces
`n^4 ≤ z`. This is not a theorem that every overshoot returns, and not
a halt theorem.
-/

theorem image_oddEvenBlock (x a b : ℕ) :
    image x (oddEvenBlock a b) =
      image (image x (List.replicate a Branch.odd))
        (List.replicate b Branch.even) :=
  image_append x (List.replicate a Branch.odd) (List.replicate b Branch.even)

theorem first_even_return {x a : ℕ} (hw : follows x (oddEvenBlock a 1)) :
    image x (List.replicate a Branch.odd) % 2 = 0 :=
  odd_run_even_residual hw

theorem image_odd_run (n a : ℕ) :
    image n (List.replicate a Branch.odd) = floorPower^[a] n := by
  simpa [List.length_replicate] using image_eq_iterate n (List.replicate a Branch.odd)

theorem even_floorPower_lt_iff {z n : ℕ} (heven : z % 2 = 0) :
    floorPower z < n ↔ z < n ^ 2 := by
  rw [floorPower_even_eq heven]
  simpa [pow_two] using (@Nat.sqrt_lt z n)

theorem even_floorPower_eq_iff {z n : ℕ} (heven : z % 2 = 0) :
    floorPower z = n ↔ n ^ 2 ≤ z ∧ z < (n + 1) ^ 2 :=
  floorPower_even_eq_iff_sq_interval heven

theorem even_floorPower_gt_iff {z n : ℕ} (heven : z % 2 = 0) :
    n < floorPower z ↔ (n + 1) ^ 2 ≤ z := by
  have hiff : floorPower z < n + 1 ↔ z < (n + 1) ^ 2 :=
    even_floorPower_lt_iff (n := n + 1) heven
  constructor
  · intro h
    have : ¬floorPower z < n + 1 := Nat.not_lt.mpr (Nat.succ_le_of_lt h)
    exact Nat.le_of_not_lt (hiff.not.mp this)
  · intro h
    have : ¬floorPower z < n + 1 := hiff.not.mpr (Nat.not_lt.mpr h)
    exact Nat.lt_of_succ_le (Nat.le_of_not_lt this)

theorem even_ge_sq_image_ge {z n : ℕ} (heven : z % 2 = 0)
    (h : n ^ 2 ≤ z) : n ≤ floorPower z := by
  rw [floorPower_even_eq heven]
  exact Nat.le_sqrt.mpr (by simpa [pow_two] using h)

/-- An even residual versus an odd start sits in exactly one cell. -/
theorem odd_even_residual_trichotomy {z n : ℕ}
    (hodd : n % 2 = 1) (heven : z % 2 = 0) :
    z < n ^ 2 ∨ (n ^ 2 < z ∧ z < (n + 1) ^ 2) ∨ (n + 1) ^ 2 ≤ z := by
  rcases lt_or_ge z (n ^ 2) with hlt | hge
  · exact Or.inl hlt
  · have hne : z ≠ n ^ 2 := even_ne_odd_square heven hodd
    have hgt : n ^ 2 < z := lt_of_le_of_ne hge hne.symm
    rcases lt_or_ge z ((n + 1) ^ 2) with hcell | hover
    · exact Or.inr (Or.inl ⟨hgt, hcell⟩)
    · exact Or.inr (Or.inr hover)

/-- Image of an even residual in each cell. -/
theorem odd_even_residual_image {z n : ℕ}
    (hodd : n % 2 = 1) (heven : z % 2 = 0) :
    (z < n ^ 2 ∧ floorPower z < n) ∨
      (n ^ 2 < z ∧ z < (n + 1) ^ 2 ∧ floorPower z = n) ∨
        ((n + 1) ^ 2 ≤ z ∧ n < floorPower z) := by
  rcases odd_even_residual_trichotomy hodd heven with hlt | hmid | hover
  · exact Or.inl ⟨hlt, (even_floorPower_lt_iff heven).mpr hlt⟩
  · refine Or.inr (Or.inl ⟨hmid.1, hmid.2, ?_⟩)
    exact (even_floorPower_eq_iff heven).mpr ⟨le_of_lt hmid.1, hmid.2⟩
  · exact Or.inr (Or.inr ⟨hover, (even_floorPower_gt_iff heven).mpr hover⟩)

/-- `O^a E` descends iff the even residual lies below `n^2`. -/
theorem first_even_descent_iff {n a : ℕ} (hw : follows n (oddEvenBlock a 1)) :
    (follows n (oddEvenBlock a 1) ∧ image n (oddEvenBlock a 1) < n) ↔
      image n (List.replicate a Branch.odd) < n ^ 2 := by
  have hz := odd_run_even_residual hw
  have himg : image n (oddEvenBlock a 1) =
      floorPower (image n (List.replicate a Branch.odd)) := by
    simp [image_oddEvenBlock, image]
  constructor
  · intro hd
    have : floorPower (image n (List.replicate a Branch.odd)) < n := by
      simpa [himg] using hd.2
    exact (even_floorPower_lt_iff hz).mp this
  · intro hlt
    refine ⟨hw, ?_⟩
    have : floorPower (image n (List.replicate a Branch.odd)) < n :=
      (even_floorPower_lt_iff hz).mpr hlt
    simpa [himg] using this

/-- Below-`n^2` first residual is `FiniteProgress` via `O^a E`. -/
theorem finiteProgress_of_first_even_below {n a : ℕ}
    (hw : follows n (oddEvenBlock a 1))
    (hlt : image n (List.replicate a Branch.odd) < n ^ 2) :
    FiniteProgress n :=
  finiteProgress_of_imageLt ((first_even_descent_iff hw).mpr hlt).1
    ((first_even_descent_iff hw).mpr hlt).2

theorem minimal_even_residual_gt_sq {n z k : ℕ} (h : MinimalNonTerm n)
    (hk : floorPower^[k] n = z) (heven : z % 2 = 0) : n ^ 2 < z := by
  have hle := minimal_nonterm_even_ge_sq h hk heven
  have hne := even_ne_odd_square heven (minimal_nonterm_odd h)
  exact lt_of_le_of_ne hle hne.symm

/-- A `MinimalNonTerm` start cannot descend on its first `O^a E`. -/
theorem minimal_nonterm_not_first_even_descent {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    ¬(follows n (oddEvenBlock a 1) ∧ image n (oddEvenBlock a 1) < n) := by
  intro hd
  have hz := odd_run_even_residual hw
  have hlt := (first_even_descent_iff hw).mp hd
  have hbar :=
    minimal_nonterm_even_ge_sq (k := a) h (image_odd_run n a).symm hz
  exact (not_lt_of_ge hbar) hlt

/-- Nor can the first `O^a E` capture `{1}`: the image stays `≥ n ≥ 12`. -/
theorem minimal_nonterm_not_first_even_capture {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    ¬(follows n (oddEvenBlock a 1) ∧ image n (oddEvenBlock a 1) = 1) := by
  intro hc
  have hz := odd_run_even_residual hw
  have himg : image n (oddEvenBlock a 1) =
      floorPower (image n (List.replicate a Branch.odd)) := by
    simp [image_oddEvenBlock, image]
  have hge : n ≤ image n (oddEvenBlock a 1) := by
    have hbar :=
      minimal_nonterm_even_ge_sq (k := a) h (image_odd_run n a).symm hz
    have : n ≤ floorPower (image n (List.replicate a Branch.odd)) :=
      even_ge_sq_image_ge hz hbar
    simpa [himg] using this
  have hn : 12 ≤ n := minimal_nonterm_ge_twelve h
  have : 12 ≤ 1 := le_trans hn (by simpa [hc.2] using hge)
  exact (by decide : ¬(12 : ℕ) ≤ 1) this

/-- First `O^a E` is not `FiniteProgress` on a minimal non-1 start. -/
theorem minimal_nonterm_not_first_even_finiteProgress {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1)) :
    ¬((follows n (oddEvenBlock a 1) ∧ image n (oddEvenBlock a 1) < n) ∨ (follows n (oddEvenBlock a 1) ∧ image n (oddEvenBlock a 1) = 1)) :=
  fun hfp =>
    hfp.elim (minimal_nonterm_not_first_even_descent h hw)
      (minimal_nonterm_not_first_even_capture h hw)

/-- Return to `n` on `O^a E` is a directed cycle. Not a cycle-impossibility
theorem. -/
theorem first_even_return_cycle {n a : ℕ}
    (_hw : follows n (oddEvenBlock a 1))
    (hret : image n (oddEvenBlock a 1) = n) :
    floorPower^[a + 1] n = n := by
  have hlen : (oddEvenBlock a 1).length = a + 1 := by
    simp [oddEvenBlock, List.length_append, List.length_replicate]
  have : image n (oddEvenBlock a 1) = floorPower^[a + 1] n := by
    rw [image_eq_iterate, hlen]
  simpa [this] using hret

/-- On a `MinimalNonTerm` start the first even residual is a return
cell (`T(z)=n`) or a strict overshoot (`T(z)>n`). -/
theorem minimal_first_even_dichotomy {n a : ℕ} (h : MinimalNonTerm n)
    (hw : follows n (oddEvenBlock a 1)) :
    (image n (oddEvenBlock a 1) = n ∧
        image n (List.replicate a Branch.odd) < (n + 1) ^ 2) ∨
      ((n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
        n < image n (oddEvenBlock a 1)) := by
  have hodd := minimal_nonterm_odd h
  have hz := odd_run_even_residual hw
  set z := image n (List.replicate a Branch.odd)
  have himg : image n (oddEvenBlock a 1) = floorPower z := by
    simp [image_oddEvenBlock, image, z]
  have hgt :=
    minimal_even_residual_gt_sq (k := a) h (image_odd_run n a).symm hz
  rcases odd_even_residual_image (z := z) hodd hz with hlt | hmid | hover
  · exact (lt_asymm hgt hlt.1).elim
  · refine Or.inl ⟨?_, hmid.2.1⟩
    simpa [himg] using hmid.2.2
  · refine Or.inr ⟨hover.1, ?_⟩
    simpa [himg] using hover.2

/-- First even residual overshoots iff the post-even image exceeds `n`. -/
theorem post_even_overshoot {z n : ℕ} (heven : z % 2 = 0) :
    (n + 1) ^ 2 ≤ z ↔ n < floorPower z :=
  (even_floorPower_gt_iff heven).symm

/-- Named starting point for residual analysis after overshoot. -/
theorem overshoot_residual_gt_start {n a : ℕ}
    (hw : follows n (oddEvenBlock a 1))
    (hover : (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd)) :
    n < image n (oddEvenBlock a 1) := by
  have hz := odd_run_even_residual hw
  have himg : image n (oddEvenBlock a 1) =
      floorPower (image n (List.replicate a Branch.odd)) := by
    simp [image_oddEvenBlock, image]
  have : n < floorPower (image n (List.replicate a Branch.odd)) :=
    (even_floorPower_gt_iff hz).mpr hover
  simpa [himg] using this

/-- The first post-overshoot state is not assumed odd. -/
theorem post_overshoot_parity (n a : ℕ) :
    image n (oddEvenBlock a 1) % 2 = 0 ∨
      image n (oddEvenBlock a 1) % 2 = 1 :=
  Nat.mod_two_eq_zero_or_one _

/-- Finite prefix from a later state that lands strictly below the
original start. Distinct from an image descent `T_w(x) < x` and from
a capture `T_w(x) = 1`. -/
def ReturnBelow (n x : ℕ) : Prop :=
  ∃ w, follows x w ∧ image x w < n

/-- A later return below the original start is `FiniteProgress` at `n`. -/
theorem finiteProgress_of_returnBelow {n : ℕ} {u : List Branch}
    (hu : follows n u) (hr : ReturnBelow n (image n u)) :
    FiniteProgress n := by
  obtain ⟨w, hw, hlt⟩ := hr
  refine finiteProgress_of_imageLt (follows_append hu hw) ?_
  simpa [image_append] using hlt

/-- Shared interface: an anchor prefix plus a later return below `n`
is finite progress. The `AboveAnchor` hypothesis records that the
prefix itself did not already drop. -/
theorem finiteProgress_of_aboveAnchor_returnBelow {n : ℕ} {u : List Branch}
    (h : AboveAnchor n u) (hr : ReturnBelow n (image n u)) :
    FiniteProgress n :=
  finiteProgress_of_returnBelow h.1 hr

/-- First full excursion `O^a E^b` with image below `n` is progress. -/
theorem finiteProgress_of_oddEven_lt {n a b : ℕ}
    (hw : follows n (oddEvenBlock a b))
    (hlt : image n (oddEvenBlock a b) < n) :
    FiniteProgress n :=
  finiteProgress_of_imageLt hw hlt

/-- A minimal non-1 trajectory never returns below its start. -/
theorem minimal_nonterm_no_returnBelow {n x k : ℕ}
    (h : MinimalNonTerm n) (hk : floorPower^[k] n = x) :
    ¬ReturnBelow n x := by
  intro ⟨w, _hw, hlt⟩
  have hexit : floorPower^[k + w.length] n = image x w := by
    rw [iterate_add_right, hk, image_eq_iterate]
  have hge : n ≤ image x w :=
    minimal_nonterm_ge_of_not_reachesOne h
      (by
        rw [← hexit]
        exact floorPower_iterate_pos h.pos _)
      (trajectory_not_reachesOne h hexit)
  exact Nat.not_lt.mpr hge hlt

theorem image_oddEvenBlock_iterate (n a b : ℕ) :
    image n (oddEvenBlock a b) = floorPower^[a + b] n := by
  have hlen : (oddEvenBlock a b).length = a + b := by
    simp [oddEvenBlock, List.length_append, List.length_replicate]
  rw [image_eq_iterate, hlen]

/-- Even post-even residual on a CE sits at scale `≥ n^2`. -/
theorem minimal_post_even_even_y_ge_sq {n a : ℕ}
    (h : MinimalNonTerm n) (_hw : follows n (oddEvenBlock a 1))
    (hy : image n (oddEvenBlock a 1) % 2 = 0) :
    n ^ 2 ≤ image n (oddEvenBlock a 1) :=
  minimal_nonterm_even_ge_sq (k := a + 1) h
    (image_oddEvenBlock_iterate n a 1).symm hy

/-- Even `y = T(z)` after the first `O^a E` already overshoots on a CE:
the return cell would require `y = n`, and `n` is odd. -/
theorem minimal_post_even_even_overshoots {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1))
    (hy : image n (oddEvenBlock a 1) % 2 = 0) :
    (n + 1) ^ 2 ≤ image n (List.replicate a Branch.odd) ∧
      n < image n (oddEvenBlock a 1) := by
  have hz := odd_run_even_residual hw
  have himg : image n (oddEvenBlock a 1) =
      floorPower (image n (List.replicate a Branch.odd)) := by
    simp [image_oddEvenBlock, image]
  have hny := minimal_post_even_even_y_ge_sq h hw hy
  have hn : 12 ≤ n := minimal_nonterm_ge_twelve h
  have hgt : n < image n (oddEvenBlock a 1) := by
    have hsq : n < n ^ 2 := by
      rw [pow_two]
      have : n * 1 < n * n :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      simpa using this
    exact lt_of_lt_of_le hsq hny
  refine ⟨?_, hgt⟩
  have : n < floorPower (image n (List.replicate a Branch.odd)) := by
    simpa [himg] using hgt
  exact (even_floorPower_gt_iff hz).mp this

/-- Even post-overshoot forces a fourth-power barrier on `z`. -/
theorem minimal_post_even_even_z_ge_fourth {n a : ℕ}
    (h : MinimalNonTerm n) (hw : follows n (oddEvenBlock a 1))
    (hy : image n (oddEvenBlock a 1) % 2 = 0) :
    n ^ 4 ≤ image n (List.replicate a Branch.odd) := by
  have hz := odd_run_even_residual hw
  set z := image n (List.replicate a Branch.odd)
  have himg : image n (oddEvenBlock a 1) = floorPower z := by
    simp [image_oddEvenBlock, image, z]
  have hny : n ^ 2 ≤ floorPower z := by
    have := minimal_post_even_even_y_ge_sq h hw hy
    simpa [himg] using this
  have hsq : floorPower z ^ 2 ≤ z := floorPower_even_sq_le hz
  have hpow : (n ^ 2) ^ 2 ≤ floorPower z ^ 2 := Nat.pow_le_pow_left hny 2
  calc
    n ^ 4 = (n ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, Nat.pow_mul]
    _ ≤ floorPower z ^ 2 := hpow
    _ ≤ z := hsq

/-!
# Residual steps and certificate propagation

A residual step is one realized `O^a E^b` excursion with `b ≥ 1`.
`ReachesOne` and a capture `T_v(y) = 1` propagate backward along a
residual word. A later `ReturnBelow` the original start is
`FiniteProgress` there. An image descent at the residual that stays
`≥` the original start is not an image descent at the start.
Persistent odd-to-odd residuals remain on the same unresolved
frontier. This is not a halt theorem and not a claim that
`FiniteProgress` at the residual implies `FiniteProgress` at the
start.
-/

/-- One realized excursion through a later even residual. Not an
infinite transition system. -/
def ResidualStep (x y : ℕ) : Prop :=
  ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
    image x (oddEvenBlock a b) = y

/-- Another odd-to-odd frontier state, strictly above the current one.
Recursion, not progress. -/
def PersistentOddResidual (x y : ℕ) : Prop :=
  ResidualStep x y ∧ x < y ∧ y % 2 = 1 ∧ floorPower y % 2 = 1

theorem residualStep_word {x y : ℕ} (h : ResidualStep x y) :
    ∃ w, follows x w ∧ image x w = y := by
  obtain ⟨_a, _b, _hb, hw, himg⟩ := h
  exact ⟨_, hw, himg⟩

/-- A residual step carries the exact global-defect identity.
`ResidualStep` itself is unchanged. -/
theorem residualStep_global_defect {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        x ^ (3 ^ a) =
          y ^ (2 ^ (a + b)) + globalDefect x (oddEvenBlock a b) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  have hid := global_defect_identity hw
  refine ⟨a, b, hb, hw, himg, ?_⟩
  simpa [himg, oddCount_oddEvenBlock, length_oddEvenBlock] using hid

theorem replicate_even_cons {b : ℕ} (hb : 1 ≤ b) :
    List.replicate b Branch.even =
      Branch.even :: List.replicate (b - 1) Branch.even := by
  cases b with
  | zero => cases hb
  | succ b => simp [List.replicate_succ]

/-- A residual block with a nonempty odd run has its first defect inside
that run. The first-defect contribution bound is `firstDefect_contribution`. -/
theorem residualStep_firstDefect {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        (0 < a → firstDefect x (oddEvenBlock a b) < a) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  refine ⟨a, b, hb, hw, himg, ?_⟩
  intro ha
  have hform :
      oddEvenBlock a b =
        List.replicate a Branch.odd ++
          Branch.even :: List.replicate (b - 1) Branch.even := by
    simp [oddEvenBlock, replicate_even_cons hb]
  have hw' :
      follows x
        (List.replicate a Branch.odd ++
          Branch.even :: List.replicate (b - 1) Branch.even) := by
    simpa [hform] using hw
  have hlt := firstDefect_lt_of_odd_run_then_even ha hw'
  simpa [hform] using hlt

theorem residualStep_amplify {x y : ℕ} (h : ResidualStep x y) :
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        ∀ hpos : firstDefect x (oddEvenBlock a b) < (oddEvenBlock a b).length,
          (branchDefect
              (oddEvenBlock a b)[firstDefect x (oddEvenBlock a b)]
              (floorPower^[firstDefect x (oddEvenBlock a b)] x)) ^
            (2 ^ firstDefect x (oddEvenBlock a b)) ≤
            globalDefect x (oddEvenBlock a b) := by
  obtain ⟨a, b, hb, hw, himg⟩ := h
  exact ⟨a, b, hb, hw, himg, fun hpos => firstDefect_contribution hw hpos⟩

/-- Any certified residual closes `ReachesOne` at the source. Stronger
than requiring a capture of the residual word itself. -/
theorem reachesOne_of_residualStep {x y : ℕ}
    (h : ResidualStep x y) (hy : ReachesOne y) : ReachesOne x := by
  obtain ⟨w, _hw, himg⟩ := residualStep_word h
  rw [← himg] at hy
  exact reachesOne_of_image hy

theorem finiteProgress_of_residual_capture {x y : ℕ} {v : List Branch}
    (h : ResidualStep x y) (hc : (follows y v ∧ image y v = 1)) : FiniteProgress x := by
  obtain ⟨w, hw, himg⟩ := residualStep_word h
  rw [← himg] at hc
  exact finiteProgress_of_capture (capture_of_suffix hw hc.1 hc.2).1
    (capture_of_suffix hw hc.1 hc.2).2

theorem finiteProgress_of_residual_returnBelow {x y : ℕ}
    (h : ResidualStep x y) (hr : ReturnBelow x y) : FiniteProgress x := by
  obtain ⟨w, hw, himg⟩ := residualStep_word h
  rw [← himg] at hr
  exact finiteProgress_of_returnBelow hw hr

/-- Concatenating a residual descent that stays at or above `x` is not
an image descent at `x`. Distinguishes `T_v(y) < y` from `T_v(y) < x`. -/
theorem residual_descent_not_below {x y : ℕ} {u v : List Branch}
    (_hu : follows x u) (hy : image x u = y)
    (_hd : (follows y v ∧ image y v < y)) (hge : x ≤ image y v) :
    ¬(follows x (u ++ v) ∧ image x (u ++ v) < x) := by
  intro hD
  have himg : image x (u ++ v) = image y v := by
    rw [image_append, hy]
  have : image y v < x := by
    simpa [himg] using hD.2
  exact Nat.not_lt.mpr hge this

theorem persistent_odd_odd {x y : ℕ} (h : PersistentOddResidual x y) :
    y % 2 = 1 ∧ floorPower y % 2 = 1 :=
  ⟨h.2.2.1, h.2.2.2⟩

theorem persistent_residual_gt {x y : ℕ} (h : PersistentOddResidual x y) :
    x < y :=
  h.2.1

/-- The same frontier analysis applies to a persistent residual.
This is recursion, not a progress certificate. -/
theorem persistent_residual_preserves_frontier {x y : ℕ}
    (h : PersistentOddResidual x y) :
    y % 2 = 1 ∧ floorPower y % 2 = 1 :=
  persistent_odd_odd h

theorem minimal_residual_image_ge {n y : ℕ}
    (h : MinimalNonTerm n) (hs : ResidualStep n y) : n ≤ y := by
  obtain ⟨w, hw, himg⟩ := residualStep_word hs
  simpa [himg] using minimal_nonterm_image_ge h hw

/-- Combined residual scale on a CE: odd exits stay `≥ n`, even exits
stay `≥ n^2`. -/
theorem minimal_residual_scale {n y : ℕ}
    (h : MinimalNonTerm n) (hs : ResidualStep n y) :
    n ≤ y ∧ (y % 2 = 0 → n ^ 2 ≤ y) := by
  refine ⟨minimal_residual_image_ge h hs, ?_⟩
  intro hy
  obtain ⟨w, hw, himg⟩ := residualStep_word hs
  rw [← himg] at hy
  have := minimal_nonterm_first_even_ge_sq h hw hy
  rwa [himg] at this

/-- Finite residual chains. Not an infinite-path type. -/
inductive ResidualChain : ℕ → ℕ → Prop where
  | refl (x : ℕ) : ResidualChain x x
  | step {x y z : ℕ} : ResidualStep x y → ResidualChain y z → ResidualChain x z

theorem residualChain_word {x y : ℕ} (h : ResidualChain x y) :
    ∃ w, follows x w ∧ image x w = y := by
  induction h with
  | refl x => exact ⟨[], trivial, rfl⟩
  | step hs _ ih =>
      obtain ⟨u, hu, hul⟩ := residualStep_word hs
      obtain ⟨v, hv, hvl⟩ := ih
      refine ⟨u ++ v, follows_append hu (by simpa [hul] using hv), ?_⟩
      rw [image_append, hul, hvl]

theorem reachesOne_of_residualChain {x y : ℕ}
    (h : ResidualChain x y) (hy : ReachesOne y) : ReachesOne x := by
  obtain ⟨w, _hw, himg⟩ := residualChain_word h
  rw [← himg] at hy
  exact reachesOne_of_image hy

theorem finiteProgress_of_residualChain_returnBelow {x y : ℕ}
    (h : ResidualChain x y) (hr : ReturnBelow x y) : FiniteProgress x := by
  obtain ⟨w, hw, himg⟩ := residualChain_word h
  rw [← himg] at hr
  exact finiteProgress_of_returnBelow hw hr

theorem finiteProgress_of_residualChain_capture {x y : ℕ} {v : List Branch}
    (h : ResidualChain x y) (hc : (follows y v ∧ image y v = 1)) : FiniteProgress x := by
  obtain ⟨w, hw, himg⟩ := residualChain_word h
  rw [← himg] at hc
  exact finiteProgress_of_capture (capture_of_suffix hw hc.1 hc.2).1
    (capture_of_suffix hw hc.1 hc.2).2

/-!
# Residual path regimes: repeats, cycles, envelopes

A residual step is already `ResidualStep`. This module records the
finite bounded-path consequence (a repeated trajectory state is a cycle)
and the cycle-word envelope `2^r < 3^o`. A residual return
`ResidualStep x x` therefore needs `a ≥ 2`. This is not a halt
theorem, not a cycle-impossibility theorem, and not an infinite-path
type.
-/

def ResidualDescent (x y : ℕ) : Prop :=
  ResidualStep x y ∧ y < x

def ResidualReturn (x y : ℕ) : Prop :=
  ResidualStep x y ∧ y = x

def ResidualOvershoot (x y : ℕ) : Prop :=
  ResidualStep x y ∧ x < y

/-- A repeated iterate is a finite Juggler cycle at that state. -/
theorem trajectory_repeat_cycle {n i j : ℕ} (hij : i ≤ j)
    (h : floorPower^[i] n = floorPower^[j] n) :
    floorPower^[j - i] (floorPower^[i] n) = floorPower^[i] n := by
  have hsum : i + (j - i) = j := Nat.add_sub_cancel' hij
  calc
    floorPower^[j - i] (floorPower^[i] n)
        = floorPower^[i + (j - i)] n := (iterate_add_right n i (j - i)).symm
    _ = floorPower^[j] n := by rw [hsum]
    _ = floorPower^[i] n := h.symm

/-- A residual return is an actual cycle of length `a + b`. -/
theorem residual_return_cycle {x a b : ℕ}
    (_hw : follows x (oddEvenBlock a b))
    (hret : image x (oddEvenBlock a b) = x) :
    floorPower^[a + b] x = x := by
  rw [← image_oddEvenBlock_iterate, hret]

theorem residual_return_envelope {x a b : ℕ}
    (hx : 2 ≤ x) (hb : 1 ≤ b) (hw : follows x (oddEvenBlock a b))
    (hret : image x (oddEvenBlock a b) = x) :
    2 ^ (a + b) ≤ 3 ^ a ∧ 2 ^ (a + b) < 3 ^ a := by
  have hlen := length_oddEvenBlock a b
  have hodd := oddCount_oddEvenBlock a b
  have hle : 2 ^ (oddEvenBlock a b).length ≤ 3 ^ oddCount (oddEvenBlock a b) :=
    cycle_envelope hx hw hret
  have hlt : 2 ^ (oddEvenBlock a b).length < 3 ^ oddCount (oddEvenBlock a b) :=
    cycle_strict_envelope hx hw hret (by
      rw [hlen]
      omega)
  constructor
  · simpa [hlen, hodd] using hle
  · simpa [hlen, hodd] using hlt

/-- Residual period-1 on `x ≥ 2` cannot start with `a ≤ 1`. -/
theorem residual_return_a_ge_two {x a b : ℕ}
    (hx : 2 ≤ x) (hb : 1 ≤ b) (hw : follows x (oddEvenBlock a b))
    (hret : image x (oddEvenBlock a b) = x) : 2 ≤ a := by
  have hle := (residual_return_envelope hx hb hw hret).1
  have hmon : 2 ^ (a + 1) ≤ 2 ^ (a + b) :=
    Nat.pow_le_pow_right (by decide : (1 : ℕ) ≤ 2) (Nat.add_le_add_left hb a)
  have : 2 ^ (a + 1) ≤ 3 ^ a := le_trans hmon hle
  exact two_pow_succ_le_three_pow_iff.mp this

/-- A residual chain from a CE stays at or above the start. -/
theorem minimal_residual_chain_ge {n y : ℕ}
    (h : MinimalNonTerm n) (hc : ResidualChain n y) : n ≤ y := by
  obtain ⟨w, hw, himg⟩ := residualChain_word hc
  simpa [himg] using minimal_nonterm_image_ge h hw

/-- Finite pigeonhole: a prefix valued in `[lo, hi]` that is longer
than the interval cannot be nodup. This is the finite form of
“bounded residual path ⇒ repeat”. -/
theorem bounded_prefix_not_nodup {lo hi : ℕ} (hle : lo ≤ hi)
    (xs : List ℕ) (hmem : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi)
    (hlen : hi + 1 - lo < xs.length) : ¬xs.Nodup := by
  intro hn
  have hsubset : xs.toFinset ⊆ Finset.Icc lo hi := by
    intro x hx
    exact Finset.mem_Icc.mpr (hmem x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsubset
  have hIcc : (Finset.Icc lo hi).card = hi + 1 - lo := by
    let emb : ℕ ↪ ℕ := ⟨fun i => i + lo, add_left_injective lo⟩
    have hmap : Finset.Icc lo hi = (Finset.range (hi + 1 - lo)).map emb := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        refine Finset.mem_map.mpr ⟨x - lo, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · change x - lo + lo = x
          exact Nat.sub_add_cancel hlo
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨i, himem, heq⟩
        have hi' : i < hi + 1 - lo := Finset.mem_range.mp himem
        have hsum : i + lo = x := by
          simpa [emb] using heq
        have hlo : lo ≤ x := by
          rw [← hsum]
          exact Nat.le_add_left lo i
        have hhi : x ≤ hi := by
          rw [← hsum]
          have : i + lo < hi + 1 - lo + lo := Nat.add_lt_add_right hi' lo
          have hcancel : hi + 1 - lo + lo = hi + 1 :=
            Nat.sub_add_cancel (Nat.le_succ_of_le hle)
          rw [hcancel] at this
          exact Nat.lt_succ_iff.mp this
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
    rw [hmap, Finset.card_map, Finset.card_range]
  have hlen' : xs.toFinset.card = xs.length := List.toFinset_card_of_nodup hn
  omega

/-- Persistent odd-to-odd residual whose block is formally expanding.
Not a claim that a second such block is impossible. -/
def PersistentExpandingResidual (x y : ℕ) : Prop :=
  PersistentOddResidual x y ∧
    ∃ a b, 1 ≤ b ∧ follows x (oddEvenBlock a b) ∧
      image x (oddEvenBlock a b) = y ∧
        exponentExpanding (oddEvenBlock a b)

theorem persistent_expanding_of {x y a b : ℕ}
    (hb : 1 ≤ b) (hw : follows x (oddEvenBlock a b))
    (himg : image x (oddEvenBlock a b) = y)
    (hgt : x < y) (hy : y % 2 = 1) (ht : floorPower y % 2 = 1)
    (hexp : exponentExpanding (oddEvenBlock a b)) :
    PersistentExpandingResidual x y :=
  ⟨⟨⟨a, b, hb, hw, himg⟩, hgt, hy, ht⟩, a, b, hb, hw, himg, hexp⟩

theorem persistent_expanding_endpoint_odd_odd {x y : ℕ}
    (h : PersistentExpandingResidual x y) :
    y % 2 = 1 ∧ floorPower y % 2 = 1 :=
  ⟨h.1.2.2.1, h.1.2.2.2⟩

/-- A persistent residual endpoint is odd-to-odd, so the next residual
block has at least two odd letters. This does not force that block to
be exponent-contracting. -/
theorem persistent_next_odd_run_two {y a b : ℕ}
    (hy : y % 2 = 1) (ht : floorPower y % 2 = 1)
    (hb : 1 ≤ b) (hw : follows y (oddEvenBlock a b)) : 2 ≤ a := by
  have ha : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    have hw' : follows y (List.replicate b Branch.even) := by
      simpa [oddEvenBlock, ha0] using hw
    have heven : y % 2 = 0 := by
      cases b with
      | zero => cases hb
      | succ b =>
          simpa [List.replicate_succ] using hw'.1
    omega
  by_contra h2
  have ha1 : a = 1 := by omega
  have hw' :
      follows y (Branch.odd :: List.replicate b Branch.even) := by
    simpa [oddEvenBlock, ha1] using hw
  have heven : floorPower y % 2 = 0 := by
    cases b with
    | zero => cases hb
    | succ b =>
        simpa [List.replicate_succ] using hw'.2.1
  omega

theorem persistent_expanding_next_min_odds {x y a b : ℕ}
    (h : PersistentExpandingResidual x y)
    (hb : 1 ≤ b) (hw : follows y (oddEvenBlock a b)) : 2 ≤ a :=
  persistent_next_odd_run_two h.1.2.2.1 h.1.2.2.2 hb hw

theorem oddEvenBlock_two_one :
    oddEvenBlock 2 1 = [.odd, .odd, .even] := by
  simp [oddEvenBlock]

theorem ooe_is_expanding : exponentExpanding (oddEvenBlock 2 1) := by
  rw [exponentExpanding_oddEvenBlock]
  decide

/-- Smallest odd-odd start of two consecutive expanding persistent
`OOE` blocks. This kills the two-block impossibility. -/
theorem follows_oddEvenBlock_two_one {n : ℕ}
    (h : word n 3 = [.odd, .odd, .even]) :
    follows n (oddEvenBlock 2 1) := by
  have hlen : (oddEvenBlock 2 1).length = 3 := length_oddEvenBlock 2 1
  have hw : word n (oddEvenBlock 2 1).length = oddEvenBlock 2 1 := by
    rw [hlen, oddEvenBlock_two_one, h]
  exact (follows_iff_word n _).mpr hw

theorem image_oddEvenBlock_two_one {n y : ℕ}
    (h : floorPower^[3] n = y) :
    image n (oddEvenBlock 2 1) = y := by
  simpa [image_eq_iterate, length_oddEvenBlock] using h

theorem two_block_ooe_365 :
    PersistentExpandingResidual 365 763 ∧
      PersistentExpandingResidual 763 1749 := by
  have w365 : word 365 3 = [.odd, .odd, .even] := by native_decide
  have w763 : word 763 3 = [.odd, .odd, .even] := by native_decide
  have i365 : floorPower^[3] 365 = 763 := by native_decide
  have i763 : floorPower^[3] 763 = 1749 := by native_decide
  have h365 := follows_oddEvenBlock_two_one w365
  have h763 := follows_oddEvenBlock_two_one w763
  have hy : (763 : ℕ) % 2 = 1 := by native_decide
  have ht : floorPower 763 % 2 = 1 := by native_decide
  have hz : (1749 : ℕ) % 2 = 1 := by native_decide
  have htz : floorPower 1749 % 2 = 1 := by native_decide
  exact ⟨
    persistent_expanding_of (by decide) h365
      (image_oddEvenBlock_two_one i365) (by decide) hy ht ooe_is_expanding,
    persistent_expanding_of (by decide) h763
      (image_oddEvenBlock_two_one i763) (by decide) hz htz ooe_is_expanding⟩

theorem two_consecutive_persistent_expanding_exists :
    ∃ x y z, PersistentExpandingResidual x y ∧
      PersistentExpandingResidual y z :=
  ⟨365, 763, 1749, two_block_ooe_365⟩

/-- Research wrapper of `global_defect_le_surplus_of_expanding`.
Reparameterization of `T_w(n) ≥ n`, not a canonical Minimal fact. -/
theorem minimal_nonterm_global_defect_le_surplus {n : ℕ} {w : List Branch}
    (h : MinimalNonTerm n) (hw : follows n w) :
    globalDefect n w + n ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) :=
  global_defect_le_surplus_of_expanding hw (minimal_nonterm_image_ge h hw)

end Problems.Juggler
