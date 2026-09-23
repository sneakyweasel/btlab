import Problems.Collatz.PreimageBalance
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

/-! # Finite-path packing for both signed Collatz maps

The classical parity-residue packing argument is applied before the last
iteration window of a finite nonrepeating path. This retains preperiodic paths.
The quantitative split uses five steps per scale, as in M. Sharpe's
`Collatz/OrbitPacking.lean`; the signed moment proof below is independent.
Adapted packing portions: Copyright (c) 2026 M. Sharpe, MIT license;
see `literature/licenses/msharpe248-collatz-MIT.txt` in the repository root.
-/

noncomputable section

namespace Problems.Collatz.SignedOrbitPacking

open Finset
open scoped Classical

/-- Shortcut dynamics for both signs. On odd inputs the false branch is
`(3*n-1)/2`, written using natural floor division. -/
def step (plus : Bool) (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3*n + if plus then 1 else 0) / 2

/-- Number of odd source states in a finite shortcut path. -/
def oddCount (plus : Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => (if n % 2 = 0 then 0 else 1) + oddCount plus k (step plus n)

/-- Both signed shortcut maps halve an even input. -/
theorem step_even (plus : Bool) (n : ℕ) : step plus (2*n) = n := by
  simp [step]

/-- An odd input has affine image `3*n+2` for the plus sign and `3*n+1` for minus. -/
theorem step_odd (plus : Bool) (n : ℕ) :
    step plus (2*n+1) = 3*n + if plus then 2 else 1 := by
  cases plus <;> simp [step] <;> omega

private theorem half_congr {a b M : ℕ} (h : a ≡ b [MOD 2*M]) :
    a/2 ≡ b/2 [MOD M] := by
  change a / 2 % M = b / 2 % M
  rw [← Nat.mod_mul_left_div_self, ← Nat.mod_mul_left_div_self]
  simpa [Nat.mul_comm] using congrArg (fun n => n/2) h

/-- One shortcut step preserves congruence after dropping one binary digit of precision. -/
theorem step_congr (plus : Bool) {k a b : ℕ} (h : a ≡ b [MOD 2^(k+1)]) :
    step plus a ≡ step plus b [MOD 2^k] := by
  have h2 : a % 2 = b % 2 := h.of_dvd (dvd_pow_self 2 (by omega))
  have hm : a ≡ b [MOD 2*2^k] := by simpa [pow_succ, Nat.mul_comm] using h
  unfold step
  rw [h2]
  by_cases he : b % 2 = 0
  · simp only [he, ↓reduceIte]; exact half_congr hm
  · simp only [he, ↓reduceIte]; exact half_congr ((hm.mul_left 3).add_right _)

/-- Odd counts depend only on the exact binary source residue. -/
theorem oddCount_congr (plus : Bool) (k : ℕ) {a b : ℕ}
    (h : a ≡ b [MOD 2^k]) : oddCount plus k a = oddCount plus k b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
      have h2 : a % 2 = b % 2 := h.of_dvd (dvd_pow_self 2 (by omega))
      simp only [oddCount, h2, ih (step_congr plus h)]

private theorem sum_pairs (f : ℕ → ℕ) (N : ℕ) :
    ∑ n ∈ range (2*N), f n = ∑ n ∈ range N, (f (2*n)+f (2*n+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 2*(N+1) = (2*N+1)+1 by omega, sum_range_succ, sum_range_succ,
        ih, sum_range_succ]
      omega

private theorem moment_affine (plus : Bool) (k b : ℕ) :
    ∑ n ∈ range (2^k), 2^oddCount plus k (3*n+b) =
      ∑ n ∈ range (2^k), 2^oddCount plus k n := by
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  let e : Fin (2^k) ≃ Fin (2^k) := Equiv.ofBijective
    (PreimageBalance.affine (by positivity) 3 b)
    (PreimageBalance.affine_bijective (by positivity) 3 b
      ((by norm_num : Nat.Coprime 2 3).pow_left k))
  have he := e.sum_comp (fun n : Fin (2^k) => 2^oddCount plus k n.val)
  have hp (n : ℕ) : oddCount plus k ((3*n+b) % 2^k) = oddCount plus k (3*n+b) :=
    oddCount_congr plus k (Nat.mod_modEq _ _)
  simpa only [e, Equiv.ofBijective_apply, PreimageBalance.affine, hp,
    Fin.sum_univ_eq_sum_range] using he

/-- The complete residue moment is exactly three to the depth, for either sign. -/
theorem parity_moment (plus : Bool) (k : ℕ) :
    ∑ n ∈ range (2^k), 2^oddCount plus k n = 3^k := by
  induction k with
  | zero => simp [oddCount]
  | succ k ih =>
      rw [pow_succ, Nat.mul_comm (2^k) 2, sum_pairs]
      simp only [oddCount, Nat.mul_mod_right, ↓reduceIte, step_even, zero_add,
        Nat.add_mod, Nat.mul_mod_right, Nat.reduceMod,
        Nat.one_ne_zero, step_odd, pow_add, pow_one]
      rw [sum_add_distrib, ← mul_sum, moment_affine, ih]
      omega

/-- One-sided source tail; no independence assumption on a selected orbit. -/
theorem odd_tail (plus : Bool) (k q : ℕ) :
    2^q * ((range (2^k)).filter (fun n => q ≤ oddCount plus k n)).card ≤ 3^k := by
  let s := (range (2^k)).filter (fun n => q ≤ oddCount plus k n)
  calc
    2^q*s.card = ∑ n ∈ s, 2^q := by simp [Nat.mul_comm]
    _ ≤ ∑ n ∈ s, 2^oddCount plus k n := sum_le_sum (fun n hn =>
      Nat.pow_le_pow_right (by decide) (mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ range (2^k), 2^oddCount plus k n :=
      sum_le_sum_of_subset (filter_subset _ _)
    _ = _ := parity_moment plus k

/-- A coarse affine envelope sufficient for packing at a complete binary scale. -/
theorem endpoint_bound (plus : Bool) (k n : ℕ) :
    2^k * (step plus)^[k] n ≤ 3^oddCount plus k n * (n+2^k) := by
  induction k generalizing n with
  | zero => simp [oddCount]
  | succ k ih =>
      rw [Function.iterate_succ_apply, oddCount]
      have hi := ih (step plus n)
      by_cases he : n % 2 = 0
      · simp only [he, ↓reduceIte, zero_add]
        have hs : 2*step plus n ≤ n := by simp [step, he]; omega
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_left (3^oddCount plus k (step plus n)) hs]
      · simp only [he, ↓reduceIte, pow_add, pow_one]
        have hs : 2*step plus n ≤ 3*n+1 := by
          cases plus <;> simp [step, he] <;> omega
        have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
        nlinarith [Nat.mul_le_mul_left (3^oddCount plus k (step plus n)) hs,
          Nat.mul_le_mul_left (3^oddCount plus k (step plus n)) hp]

/-- Starting below `2^k` bounds the endpoint by twice three to the odd-step count. -/
theorem small_endpoint (plus : Bool) {k n : ℕ} (hn : n < 2^k) :
    (step plus)^[k] n < 2*3^oddCount plus k n := by
  have he := endpoint_bound plus k n
  have hp : 0 < 2^k := by positivity
  have hq : 0 < 3^oddCount plus k n := by positivity
  nlinarith

/-- Equal-time injectivity and the exact residue moment give a power saving. -/
theorem packing_bound (plus : Bool) {m : ℕ} {s : Finset ℕ}
    (hs : s ⊆ range (32^m)) (hi : Set.InjOn ((step plus)^[5*m]) s) :
    8^m*s.card ≤ 2*216^m+243^m := by
  let lo := s.filter (fun n => oddCount plus (5*m) n < 3*m)
  let high := s.filter (fun n => 3*m ≤ oddCount plus (5*m) n)
  have hp : 2^(5*m) = 32^m := by rw [pow_mul]; norm_num
  have hlo : lo.card ≤ 2*27^m := by
    have hmap : Set.MapsTo ((step plus)^[5*m]) lo (range (2*27^m)) := by
      intro n hn
      have hh := mem_filter.mp hn
      have he := small_endpoint plus (k := 5*m) (by
        rw [hp]; exact mem_range.mp (hs hh.1))
      have hpow : 3^oddCount plus (5*m) n ≤ 27^m := by
        calc
          _ ≤ 3^(3*m) := Nat.pow_le_pow_right (by decide) hh.2.le
          _ = _ := by rw [pow_mul]; norm_num
      exact mem_range.mpr (by omega)
    simpa using card_le_card_of_injOn _ hmap (hi.mono (filter_subset _ _))
  have hhigh : 8^m*high.card ≤ 243^m := by
    have hsub : high ⊆ (range (2^(5*m))).filter (fun n => 3*m ≤ oddCount plus (5*m) n) := by
      intro n hn
      exact mem_filter.mpr ⟨by rw [hp]; exact hs (mem_filter.mp hn).1,
        (mem_filter.mp hn).2⟩
    have hb := (Nat.mul_le_mul_left (2^(3*m)) (card_le_card hsub)).trans
      (odd_tail plus (5*m) (3*m))
    simpa [pow_mul] using hb
  have hc : lo.card + high.card = s.card := by
    simpa [lo, high, Nat.not_lt] using
      card_filter_add_card_filter_not (s := s) (p := fun n => oddCount plus (5*m) n < 3*m)
  have he : 8^m * (2*27^m) = 2*216^m := by
    rw [show 216 = 8*27 by decide, mul_pow]; ring
  nlinarith [Nat.mul_le_mul_left (8^m) hlo,
    congrArg (fun z => 8^m*z) hc]

/-- The final window is the only part of a nonrepeating finite path on which
equal-time images may merge after the end of the path. -/
theorem finite_path_packing (plus : Bool) {N n m : ℕ} {s : Finset ℕ}
    (hs : s ⊆ range (32^m))
    (hp : ∀ x ∈ s, ∃ i < N, (step plus)^[i] n = x)
    (hi : Set.InjOn (fun i => (step plus)^[i] n) (range N)) :
    8^m*s.card ≤ 2*216^m+243^m+8^m*(5*m) := by
  let early := s.filter (fun x => ∃ i < N-5*m, (step plus)^[i] n = x)
  have hinj : Set.InjOn ((step plus)^[5*m]) early := by
    intro x hx y hy he
    obtain ⟨i, hi', rfl⟩ := (mem_filter.mp hx).2
    obtain ⟨j, hj', rfl⟩ := (mem_filter.mp hy).2
    have he' : (step plus)^[5*m+i] n = (step plus)^[5*m+j] n := by
      simpa only [Function.iterate_add_apply] using he
    have hij := hi (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) he'
    have : i = j := by omega
    rw [this]
  have hb := packing_bound plus ((filter_subset _ _).trans hs) hinj
  change 8^m*early.card ≤ 2*216^m+243^m at hb
  have htail : s \ early ⊆ (Ico (N-5*m) N).image (fun i => (step plus)^[i] n) := by
    intro x hx
    obtain ⟨hxs,hxe⟩ := mem_sdiff.mp hx
    obtain ⟨i, hi', he⟩ := hp x hxs
    have hil : N-5*m ≤ i := by
      by_contra h
      exact hxe (mem_filter.mpr ⟨hxs,i,by omega,he⟩)
    exact mem_image.mpr ⟨i,mem_Ico.mpr ⟨hil,hi'⟩,he⟩
  have ht : (s \ early).card ≤ 5*m := by
    have hh := (card_le_card htail).trans card_image_le
    rw [Nat.card_Ico] at hh
    omega
  have hc : (s \ early).card + early.card = s.card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  nlinarith [Nat.mul_le_mul_left (8^m) ht,
    congrArg (fun z => 8^m*z) hc]

/-- A summable shell allowance, including the finite terminal window. -/
def shellBudget (m : ℕ) : ℝ :=
  54*(27/32 : ℝ)^m + (243/8 : ℝ)*(243/256 : ℝ)^m +
    5*((m:ℝ)+1)*(1/32 : ℝ)^m

/-- Every shell allowance is nonnegative. -/
theorem shellBudget_nonneg (m : ℕ) : 0 ≤ shellBudget m := by
  unfold shellBudget; positivity

/-- The geometric decay makes the total allowance over all shells summable. -/
theorem shellBudget_summable : Summable shellBudget := by
  have h1 := (summable_geometric_of_norm_lt_one (by norm_num : ‖(27/32:ℝ)‖ < 1)).mul_left 54
  have h2 := (summable_geometric_of_norm_lt_one (by norm_num : ‖(243/256:ℝ)‖ < 1)).mul_left (243/8)
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 1
    (by norm_num : ‖(1/32:ℝ)‖ < 1)
  have h4 := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/32:ℝ)‖ < 1)
  apply ((h1.add h2).add ((h3.add h4).mul_left 5)).congr
  intro m
  dsimp [shellBudget]
  simp only [pow_one]
  ring

private theorem shellBudget_identity (m : ℕ) :
    shellBudget m * (8:ℝ)^(m+1) * 32^m =
      2*216^(m+1)+243^(m+1)+8^(m+1)*(5*((m:ℝ)+1)) := by
  have h216 : (216:ℝ)^m = 8^m*27^m := by rw [← mul_pow]; norm_num
  have h256 : (256:ℝ)^m = 8^m*32^m := by rw [← mul_pow]; norm_num
  simp only [shellBudget, div_pow, one_pow, pow_succ, h216, h256]
  field_simp
  ring

/-- One absolute bound for reciprocal mass of any positive nonrepeating finite path. -/
noncomputable def reciprocalBudget : ℝ := ∑' m, shellBudget m

/-- The total reciprocal allowance is nonnegative, as a sum of nonnegative shells. -/
theorem reciprocalBudget_nonneg : 0 ≤ reciprocalBudget :=
  tsum_nonneg shellBudget_nonneg

/-- Finite paths need no assertion about their future orbit. -/
theorem finite_path_reciprocal (plus : Bool) {N n : ℕ} {s : Finset ℕ}
    (hpos : ∀ x ∈ s, 0 < x)
    (hp : ∀ x ∈ s, ∃ i < N, (step plus)^[i] n = x)
    (hi : Set.InjOn (fun i => (step plus)^[i] n) (range N)) :
    ∑ x ∈ s, (1:ℝ)/x ≤ reciprocalBudget := by
  have hshell (m : ℕ) :
      ∑ x ∈ s.filter (fun x => Nat.log 32 x = m), (1:ℝ)/x ≤ shellBudget m := by
    let t := s.filter (fun x => Nat.log 32 x = m)
    have ht : t ⊆ range (32^(m+1)) := by
      intro x hx
      have hh := mem_filter.mp hx
      have hh' := Nat.lt_pow_succ_log_self (by decide : 1 < 32) x
      rw [hh.2] at hh'
      exact mem_range.mpr hh'
    have hb := finite_path_packing plus ht
      (fun x hx => hp x (mem_filter.mp hx).1) hi
    have hbr : (8:ℝ)^(m+1)*t.card ≤
        2*216^(m+1)+243^(m+1)+8^(m+1)*(5*((m:ℝ)+1)) := by exact_mod_cast hb
    have hlo (x : ℕ) (hx : x ∈ t) : (32:ℝ)^m ≤ x := by
      have hh := mem_filter.mp hx
      have h := Nat.pow_log_le_self 32 (hpos x hh.1).ne'
      rw [hh.2] at h
      exact_mod_cast h
    calc
      ∑ x ∈ t, (1:ℝ)/x ≤ ∑ _x ∈ t, (1:ℝ)/32^m := by
        apply sum_le_sum
        intro x hx
        exact one_div_le_one_div_of_le (by positivity) (hlo x hx)
      _ = (t.card:ℝ)/32^m := by simp [div_eq_mul_inv]
      _ ≤ shellBudget m := by
        apply (div_le_iff₀ (by positivity)).mpr
        have he := shellBudget_identity m
        have h8 : (0:ℝ) < 8^(m+1) := by positivity
        nlinarith
  rw [← sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem (Nat.log 32) hx)]
  exact (sum_le_sum (fun m _ => hshell m)).trans
    (shellBudget_summable.sum_le_tsum _ (fun m _ => shellBudget_nonneg m))

end Problems.Collatz.SignedOrbitPacking
