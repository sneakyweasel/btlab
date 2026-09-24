import Problems.Juggler.Dynamics

namespace Problems.Juggler.EscapeResidue

open Problems.Juggler

/-!
# Periodic domains cannot guard the second O of an all-OOE trajectory

Paper A, Proposition E.7. With `t = 2Qh` and `x = t^8 + a` for odd `a < Q`,
the first Juggler image is exactly `t^12 + (3a/2) t^4`, which is even, so the
second O step of an OOE block fails. Writing `k = t^4 / 2` turns the two
square margins into a polynomial identity in `k` and `a`. The consequence is
that no eventually periodic set with an odd member keeps every odd member's
first image odd. This is a restriction on proposed invariant domains, not an
escape or no-escape theorem.
-/

/-- Exact first image for sources `4k^2 + a` with `a^2 ≤ 2k`: the integer
square root of the cube is `8k^3 + 3ak`, from the margins
`x^3 - u^2 = 3a^2k^2 + a^3` and `(u+1)^2 - x^3 > 0`. -/
theorem sqrt_cube_escape_source {k a : ℕ} (hk : 1 ≤ k) (ha : a ^ 2 ≤ 2 * k) :
    ((4 * k ^ 2 + a) ^ 3).sqrt = 8 * k ^ 3 + 3 * a * k := by
  symm
  rw [Nat.eq_sqrt']
  have hlow : (4 * k ^ 2 + a) ^ 3 =
      (8 * k ^ 3 + 3 * a * k) ^ 2 + (3 * a ^ 2 * k ^ 2 + a ^ 3) := by ring
  have hhigh : (8 * k ^ 3 + 3 * a * k + 1) ^ 2 =
      (8 * k ^ 3 + 3 * a * k) ^ 2 + (16 * k ^ 3 + 6 * a * k + 1) := by ring
  have h1 : 3 * a ^ 2 * k ^ 2 ≤ 6 * k ^ 3 := by
    have := Nat.mul_le_mul_right (3 * k ^ 2) ha
    nlinarith [this]
  have haa : a ≤ a ^ 2 := by nlinarith [Nat.zero_le a]
  have h2 : a ^ 3 ≤ 4 * k ^ 3 := by
    have ha2k : a ≤ 2 * k := le_trans haa ha
    have hcube : a ^ 3 = a * a ^ 2 := by ring
    have hk2 : k ^ 2 ≤ k ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
    rw [hcube]
    calc a * a ^ 2 ≤ (2 * k) * (2 * k) := Nat.mul_le_mul ha2k ha
      _ = 4 * k ^ 2 := by ring
      _ ≤ 4 * k ^ 3 := by omega
  constructor
  · rw [hlow]; omega
  · rw [hlow, hhigh]
    have : 0 < k ^ 3 := by positivity
    omega

/-- For even `k ≥ 1`, odd `a` and `a^2 ≤ 2k`, the source `4k^2 + a` is odd and
its Juggler image `8k^3 + 3ak` is even, so an OO prefix cannot start there. -/
theorem floorPower_escape_source {k a : ℕ} (hk : 1 ≤ k) (ha : a ^ 2 ≤ 2 * k)
    (hkeven : k % 2 = 0) (haodd : a % 2 = 1) :
    (4 * k ^ 2 + a) % 2 = 1 ∧
      floorPower (4 * k ^ 2 + a) = 8 * k ^ 3 + 3 * a * k ∧
      floorPower (4 * k ^ 2 + a) % 2 = 0 := by
  have hx : (4 * k ^ 2 + a) % 2 = 1 := by omega
  have himg : floorPower (4 * k ^ 2 + a) = 8 * k ^ 3 + 3 * a * k := by
    rw [floorPower_odd_eq hx, sqrt_cube_escape_source hk ha]
  refine ⟨hx, himg, ?_⟩
  rw [himg]
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
  have : 8 * (2 * j) ^ 3 + 3 * a * (2 * j) = 2 * (32 * j ^ 3 + 3 * a * j) := by ring
  omega

/-- Paper A, Proposition E.7, explicit family. For `Q ≥ 1`, odd `a < Q` and
`h ≥ 1`, put `t = 2Qh` and `x = t^8 + a`. Then `x ≡ a (mod Q)`, `x` is odd, and
`O(x) = t^12 + 24aQ^4h^4 = t^12 + (3a/2)t^4` is even. The evenness of `Q` in
the paper only makes `a` an odd residue class; the identity does not need it. -/
theorem escape_residue_source {Q a h : ℕ} (hQ : 1 ≤ Q) (haodd : a % 2 = 1)
    (haQ : a < Q) (hh : 1 ≤ h) :
    ((2 * Q * h) ^ 8 + a) % Q = a ∧ ((2 * Q * h) ^ 8 + a) % 2 = 1 ∧
      floorPower ((2 * Q * h) ^ 8 + a) = (2 * Q * h) ^ 12 + 24 * a * Q ^ 4 * h ^ 4 ∧
      floorPower ((2 * Q * h) ^ 8 + a) % 2 = 0 := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = Q ^ 4 * h ^ 4 := ⟨_, rfl⟩
  have hm : 1 ≤ m := by
    have hQ4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
    have hh4 : 1 ≤ h ^ 4 := Nat.one_le_pow _ _ hh
    rw [hmdef]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hx : (2 * Q * h) ^ 8 = 4 * (8 * m) ^ 2 := by rw [hmdef]; ring
  have ha2 : a ^ 2 ≤ 2 * (8 * m) := by
    have hQ2 : a ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left haQ.le 2
    have hQ4 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
    have hh4 : 1 ≤ h ^ 4 := Nat.one_le_pow _ _ hh
    have : Q ^ 4 ≤ m := hmdef ▸ Nat.le_mul_of_pos_right _ hh4
    omega
  obtain ⟨hodd, himg, heven⟩ :=
    floorPower_escape_source (by omega : 1 ≤ 8 * m) ha2 (by omega) haodd
  have hmod : ((2 * Q * h) ^ 8 + a) % Q = a := by
    have hdvd : Q ∣ (2 * Q * h) ^ 8 :=
      Dvd.dvd.pow ⟨2 * h, by ring⟩ (by norm_num)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt haQ]
  have himg' : 8 * (8 * m) ^ 3 + 3 * a * (8 * m) =
      (2 * Q * h) ^ 12 + 24 * a * Q ^ 4 * h ^ 4 := by
    rw [hmdef]; ring
  refine ⟨hmod, ?_, ?_, ?_⟩
  · rw [hx]; exact hodd
  · rw [hx, himg, himg']
  · rw [hx]; exact heven

/-- Iterating an eventual period `M` from `x₀` reaches `x₀ + M * j`. -/
private theorem periodic_add_mul {P : ℕ → Prop} {M N₀ x₀ : ℕ}
    (hper : ∀ n, N₀ ≤ n → (P (n + M) ↔ P n)) (hx₀ : N₀ ≤ x₀) (hP : P x₀) :
    ∀ j, P (x₀ + M * j) := by
  intro j
  induction j with
  | zero => simpa using hP
  | succ j ih =>
      have : x₀ + M * (j + 1) = (x₀ + M * j) + M := by ring
      rw [this, hper _ (by omega)]
      exact ih

/-- Paper A, Proposition E.7. If `P` is eventually periodic with period
`M ≥ 1` beyond `N₀` and has an odd member `x₀ ≥ N₀`, then arbitrarily large odd
members of `P` have even first Juggler image. This covers every eventual union
of odd residue classes and every fixed-modulus polynomial congruence. -/
theorem exists_escape_of_periodic {P : ℕ → Prop} {M N₀ x₀ : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, N₀ ≤ n → (P (n + M) ↔ P n)) (hx₀ : N₀ ≤ x₀) (hP : P x₀)
    (hodd : x₀ % 2 = 1) (N : ℕ) :
    ∃ x, N ≤ x ∧ P x ∧ x % 2 = 1 ∧ floorPower x % 2 = 0 := by
  set Q := 2 * M with hQdef
  set a := x₀ % Q with hadef
  set h := x₀ + N + 1 with hhdef
  have hQ : 1 ≤ Q := by omega
  have haQ : a < Q := Nat.mod_lt _ (by omega)
  have haodd : a % 2 = 1 := by
    rw [hadef, hQdef, Nat.mod_mul_right_mod]; exact hodd
  obtain ⟨hmod, hxodd, -, heven⟩ := escape_residue_source hQ haodd haQ (by omega : 1 ≤ h)
  set x := (2 * Q * h) ^ 8 + a with hxdef
  have hbig : h ≤ (2 * Q * h) ^ 8 := by
    have h1 : h ≤ 2 * Q * h := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : 2 * Q * h ≤ (2 * Q * h) ^ 8 :=
      Nat.le_self_pow (by norm_num) _
    omega
  have hge : x₀ ≤ x := by omega
  have hsub : (x - x₀) % Q = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [hmod])
  obtain ⟨j, hj⟩ : Q ∣ x - x₀ := Nat.dvd_of_mod_eq_zero hsub
  have hdecomp : x = x₀ + M * (2 * j) := by
    have : M * (2 * j) = Q * j := by rw [hQdef]; ring
    omega
  refine ⟨x, by omega, ?_, hxodd, heven⟩
  rw [hdecomp]
  exact periodic_add_mul hper hx₀ hP _

/-- No nonempty eventually periodic set keeps every member odd with an odd
first image beyond its threshold, so none is a fully guarded all-OOE domain. -/
theorem not_oo_guarded_of_periodic {P : ℕ → Prop} {M N₀ x₀ : ℕ} (hM : 1 ≤ M)
    (hper : ∀ n, N₀ ≤ n → (P (n + M) ↔ P n)) (hx₀ : N₀ ≤ x₀) (hP : P x₀) :
    ¬ ∀ x, N₀ ≤ x → P x → x % 2 = 1 ∧ floorPower x % 2 = 1 := by
  intro H
  obtain ⟨x, hxN, hPx, -, heven⟩ :=
    exists_escape_of_periodic hM hper hx₀ hP (H x₀ hx₀ hP).1 N₀
  have := (H x hxN hPx).2
  omega

end Problems.Juggler.EscapeResidue
