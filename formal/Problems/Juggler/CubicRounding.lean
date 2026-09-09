import Problems.Juggler.CubicBand
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Problems.Juggler

/-!
# Cubic-band maps with a one-unit successor allowance

The integer projection below is the downward projection of a real branch
value after taking its integer floor. The altered map is distinct from the
Juggler map. Its periodic orbits do not settle the Juggler no-cycle question.
-/

/-- Odd states through the square seam, followed by even states below the cube. -/
def cubicParityDomain (b x : ℕ) : Prop :=
  b ≤ x ∧ ((x ≤ b ^ 2 ∧ x % 2 = 1) ∨
    (b ^ 2 < x ∧ x < b ^ 3 ∧ x % 2 = 0))

/-- Downward projection on the prescribed source-parity domain. -/
def cubicParityProject (b n : ℕ) : ℕ :=
  if n ≤ b ^ 2 then n - (1 - n % 2) else n - n % 2

/-- The parity-preserving altered successor. -/
def cubicRounding (b x : ℕ) : ℕ := cubicParityProject b (floorPower x)

theorem cubicParityProject_le (b n : ℕ) : cubicParityProject b n ≤ n := by
  unfold cubicParityProject
  split_ifs <;> omega

theorem cubicParityProject_loss (b n : ℕ) : n ≤ cubicParityProject b n + 1 := by
  have := Nat.mod_lt n (by decide : 0 < 2)
  unfold cubicParityProject
  split_ifs <;> omega

theorem cubicParityProject_eq_or_pred (b n : ℕ) :
    cubicParityProject b n = n ∨ cubicParityProject b n = n - 1 := by
  have := cubicParityProject_le b n
  have := cubicParityProject_loss b n
  omega

theorem cubicParityDomain_bounds {b x : ℕ} (hb : 3 ≤ b)
    (hx : cubicParityDomain b x) : b ≤ x ∧ x < b ^ 3 := by
  have hs : b ^ 2 < b ^ 3 := by nlinarith [sq_nonneg (b : ℤ)]
  rcases hx with ⟨hbx, hl | hr⟩
  · exact ⟨hbx, lt_of_le_of_lt hl.1 hs⟩
  · exact ⟨hbx, hr.2.1⟩

theorem cubicParityDomain_base {b : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1) :
    cubicParityDomain b b := by
  refine ⟨le_rfl, Or.inl ⟨?_, ho⟩⟩
  nlinarith

theorem cubicParityProject_mem {b n : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1)
    (hn : b ≤ n) (hn' : n ≤ b ^ 3) :
    cubicParityDomain b (cubicParityProject b n) := by
  have hb2 : b ^ 2 % 2 = 1 := by simp [Nat.pow_mod, ho]
  have hb3 : b ^ 3 % 2 = 1 := by simp [Nat.pow_mod, ho]
  have hn2 := Nat.mod_two_eq_zero_or_one n
  have hs : b ≤ b ^ 2 := by nlinarith
  unfold cubicParityProject cubicParityDomain
  split_ifs with h
  · rcases hn2 with he | he <;> simp only [he] <;> omega
  · rcases hn2 with he | he <;> simp only [he] <;> omega

theorem cubicParityProject_fix {b x : ℕ} (hx : cubicParityDomain b x) :
    cubicParityProject b x = x := by
  rcases hx with ⟨_, hl | hr⟩
  · simp [cubicParityProject, hl.1, hl.2]
  · simp [cubicParityProject, not_le.mpr hr.1, hr.2.2]

/-- This is the largest permitted integer below the input. -/
theorem cubicParityProject_greatest {b n d : ℕ}
    (hd : cubicParityDomain b d) (hdn : d ≤ n) :
    d ≤ cubicParityProject b n := by
  rcases hd with ⟨_, hl | hr⟩
  · unfold cubicParityProject
    split_ifs <;> have := Nat.mod_two_eq_zero_or_one n <;> omega
  · unfold cubicParityProject
    split_ifs <;> have := Nat.mod_two_eq_zero_or_one n <;> omega

theorem cubicRounding_floor_range {b x : ℕ} (_hb : 3 ≤ b)
    (hx : cubicParityDomain b x) : b ≤ floorPower x ∧ floorPower x ≤ b ^ 3 := by
  rcases hx with ⟨hbx, hl | hr⟩
  · refine ⟨le_trans hbx (floorPower_odd_nondecreasing (by omega) hl.2), ?_⟩
    rw [floorPower_odd_eq hl.2]
    have hs := Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hl.1 3)
    have hp : (b ^ 2) ^ 3 = (b ^ 3) ^ 2 := by ring
    simpa only [hp, Nat.sqrt_eq'] using hs
  · rw [floorPower_even_eq hr.2.2]
    refine ⟨Nat.le_sqrt'.mpr (by omega), ?_⟩
    exact le_trans (Nat.sqrt_le_self x) (by omega)

theorem cubicRounding_mem {b x : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1)
    (hx : cubicParityDomain b x) : cubicParityDomain b (cubicRounding b x) := by
  obtain ⟨hl, hu⟩ := cubicRounding_floor_range hb hx
  exact cubicParityProject_mem hb ho hl hu

theorem cubicRounding_eq_or_pred (b x : ℕ) :
    cubicRounding b x = floorPower x ∨ cubicRounding b x = floorPower x - 1 :=
  cubicParityProject_eq_or_pred b (floorPower x)

/-- Exact integer cells express the one-sided real rounding loss below two. -/
theorem cubicRounding_square_cells (b x : ℕ) :
    cubicRounding b x ^ 2 ≤ (if x % 2 = 0 then x else x ^ 3) ∧
    (if x % 2 = 0 then x else x ^ 3) < (cubicRounding b x + 2) ^ 2 := by
  let r := if x % 2 = 0 then x else x ^ 3
  have hJ : floorPower x = r.sqrt := by
    unfold floorPower r
    split_ifs <;> rfl
  have hlo : cubicRounding b x ≤ r.sqrt := by
    simpa [cubicRounding, hJ] using cubicParityProject_le b (floorPower x)
  have hhi : r.sqrt + 1 ≤ cubicRounding b x + 2 := by
    have := cubicParityProject_loss b (floorPower x)
    change _ ≤ cubicRounding b x + 1 at this
    omega
  refine ⟨le_trans (Nat.pow_le_pow_left hlo 2) (Nat.sqrt_le' r), ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_sqrt' r) (Nat.pow_le_pow_left hhi 2)

theorem cubicRounding_same_branch_mono {b x y : ℕ} (hb : 3 ≤ b)
    (ho : b % 2 = 1) (hx : cubicParityDomain b x)
    (hp : x % 2 = y % 2) (hxy : x ≤ y) :
    cubicRounding b x ≤ cubicRounding b y := by
  apply cubicParityProject_greatest (cubicRounding_mem hb ho hx)
  refine le_trans (cubicParityProject_le b (floorPower x)) ?_
  rcases Nat.mod_two_eq_zero_or_one x with he | he
  · exact floorPower_even_mono he (hp ▸ he) hxy
  · exact floorPower_odd_mono he (hp ▸ he) hxy

/-- The two image blocks remain weakly separated after projection. -/
theorem cubicRounding_even_le_odd {b x y : ℕ} (hb : 3 ≤ b)
    (ho : b % 2 = 1) (hx : cubicParityDomain b x) (hy : cubicParityDomain b y)
    (he : x % 2 = 0) (hyodd : y % 2 = 1) :
    cubicRounding b x ≤ cubicRounding b y := by
  apply cubicParityProject_greatest (cubicRounding_mem hb ho hx)
  refine le_trans (cubicParityProject_le b (floorPower x)) ?_
  rw [floorPower_even_eq he, floorPower_odd_eq hyodd]
  apply Nat.sqrt_le_sqrt
  exact le_trans (le_of_lt (cubicParityDomain_bounds hb hx).2)
    (Nat.pow_le_pow_left hy.1 3)

/-- A sorted invariant permutation of the altered map has the exact rank rotation. -/
theorem cubicRounding_rank_rotation {b L o : ℕ} (hb : 3 ≤ b) (hbodd : b % 2 = 1)
    (ho : o ≤ L) (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hdom : ∀ i, cubicParityDomain b (c i))
    (hcut : ∀ i, c i % 2 = 1 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = cubicRounding b (c i)) (i : Fin L) :
    (p i).val = (i.val + (L - o)) % L := by
  apply twoBlock_rank_rotation_mod ho p
  · intro a d had hd
    apply hc.lt_iff_lt.mp
    have haodd : c a % 2 = 1 := (hcut a).mpr (lt_trans had hd)
    have hdodd : c d % 2 = 1 := (hcut d).mpr hd
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep]
      exact cubicRounding_same_branch_mono hb hbodd (hdom a)
        (haodd.trans hdodd.symm) (hc.monotone (le_of_lt had))
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt had) (p.injective (hc.injective he)))
  · intro a d had ha
    apply hc.lt_iff_lt.mp
    have hnotodd : ∀ j : Fin L, o ≤ j.val → c j % 2 ≠ 1 := by
      intro j hj he
      have := (hcut j).mp he
      omega
    have hae : c a % 2 = 0 := by have := hnotodd a ha; omega
    have hde : c d % 2 = 0 := by have := hnotodd d (by omega); omega
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep]
      exact cubicRounding_same_branch_mono hb hbodd (hdom a)
        (hae.trans hde.symm) (hc.monotone (le_of_lt had))
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt had) (p.injective (hc.injective he)))
  · intro a d ha hd
    apply hc.lt_iff_lt.mp
    have hae : c a % 2 = 0 := by
      have hn : c a % 2 ≠ 1 := by intro h; have := (hcut a).mp h; omega
      omega
    have hdodd : c d % 2 = 1 := (hcut d).mpr hd
    have hle : c (p a) ≤ c (p d) := by
      rw [hstep, hstep]
      exact cubicRounding_even_le_odd hb hbodd (hdom a) (hdom d) hae hdodd
    apply lt_of_le_of_ne hle
    intro he
    have hh := p.injective (hc.injective he)
    have : a.val = d.val := congrArg Fin.val hh
    omega

/-- The odd count and cutoff are derived from the sorted source domain. -/
theorem cubicRounding_sorted_rotation {b L : ℕ} (hb : 3 ≤ b) (hbodd : b % 2 = 1)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hdom : ∀ i, cubicParityDomain b (c i))
    (hstep : ∀ i, c (p i) = cubicRounding b (c i)) :
    ∃ o ≤ L, (∀ i, c i % 2 = 1 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => c i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (L - o)) % L) := by
  obtain ⟨o, ho, hcut, hcard⟩ := sorted_threshold_cut c hc (t := b ^ 2 + 1)
  have hpar : ∀ i, c i % 2 = 1 ↔ c i < b ^ 2 + 1 := by
    intro i
    rcases hdom i with ⟨_, hl | hr⟩ <;> omega
  have hoddcut : ∀ i, c i % 2 = 1 ↔ i.val < o := fun i => (hpar i).trans (hcut i)
  refine ⟨o, ho, hoddcut, ?_,
    cubicRounding_rank_rotation hb hbodd ho c hc p hdom hoddcut hstep⟩
  simpa only [hpar] using hcard

/-- Any finite invariant subset on which the altered map is injective has this sorted form. -/
theorem cubicRounding_finite_invariant_rotation {b : ℕ} (hb : 3 ≤ b)
    (hbodd : b % 2 = 1) (s : Finset ℕ)
    (hdom : ∀ x ∈ s, cubicParityDomain b x)
    (hclosed : ∀ x ∈ s, cubicRounding b x ∈ s)
    (hinj : Set.InjOn (cubicRounding b) s) :
    ∃ (p : Equiv.Perm (Fin s.card)) (o : ℕ), o ≤ s.card ∧
      (∀ i, s.orderEmbOfFin rfl (p i) = cubicRounding b (s.orderEmbOfFin rfl i)) ∧
      (∀ i, s.orderEmbOfFin rfl i % 2 = 1 ↔ i.val < o) ∧
      (Finset.univ.filter (fun i => s.orderEmbOfFin rfl i % 2 = 1)).card = o ∧
      (∀ i, (p i).val = (i.val + (s.card - o)) % s.card) := by
  obtain ⟨p, hstep⟩ := sorted_invariant_permutation s (cubicRounding b) hclosed hinj
  have hd : ∀ i, cubicParityDomain b (s.orderEmbOfFin rfl i) := fun i =>
    hdom _ (s.orderEmbOfFin_mem rfl i)
  obtain ⟨o, ho, hcut, hcard, hrot⟩ := cubicRounding_sorted_rotation hb hbodd
    (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl).strictMono p hd hstep
  exact ⟨p, o, ho, hstep, hcut, hcard, hrot⟩

theorem floorPower_odd_two_le {x : ℕ} (hx : 3 ≤ x) (ho : x % 2 = 1) :
    x + 2 ≤ floorPower x := by
  rw [floorPower_odd_eq ho, Nat.le_sqrt']
  have h2 : 3 * x ^ 2 ≤ x ^ 3 := by nlinarith
  nlinarith

theorem cubicRounding_odd_gt {b x : ℕ} (hx : 3 ≤ x) (ho : x % 2 = 1) :
    x < cubicRounding b x := by
  have := floorPower_odd_two_le hx ho
  have := cubicParityProject_loss b (floorPower x)
  change x < cubicParityProject b (floorPower x)
  omega

theorem cubicRounding_even_lt {b x : ℕ} (hx : 2 ≤ x) (he : x % 2 = 0) :
    cubicRounding b x < x :=
  lt_of_le_of_lt (cubicParityProject_le b (floorPower x)) (floorPower_even_lt hx he)

theorem cubicRounding_no_fixed {b x : ℕ} (hb : 3 ≤ b)
    (hx : cubicParityDomain b x) : cubicRounding b x ≠ x := by
  rcases Nat.mod_two_eq_zero_or_one x with he | ho
  · exact ne_of_lt (cubicRounding_even_lt (by have := hx.1; omega) he)
  · exact ne_of_gt (cubicRounding_odd_gt (by have := hx.1; omega) ho)

theorem cubicRounding_iterate_mem {b x : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1)
    (hx : cubicParityDomain b x) (k : ℕ) :
    cubicParityDomain b ((cubicRounding b)^[k] x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact cubicRounding_mem hb ho ih

/-- At every odd scale there is a nontrivial periodic orbit of the altered map. -/
theorem cubicRounding_exists_periodic {b : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1) :
    ∃ x L : ℕ, cubicParityDomain b x ∧ 2 ≤ L ∧
      (cubicRounding b)^[L] x = x ∧
      ∀ k : ℕ, b ≤ (cubicRounding b)^[k] x ∧ (cubicRounding b)^[k] x < b ^ 3 := by
  classical
  let D := {x : ℕ // cubicParityDomain b x}
  let embed : D → Fin (b ^ 3) :=
    fun x => ⟨x.1, (cubicParityDomain_bounds hb x.2).2⟩
  have hinj : Function.Injective embed := by
    intro x y h
    apply Subtype.ext
    exact congrArg Fin.val h
  let : Finite D := Finite.of_injective embed hinj
  let f : D → D := fun x => ⟨cubicRounding b x.1, cubicRounding_mem hb ho x.2⟩
  let start : D := ⟨b, cubicParityDomain_base hb ho⟩
  have hval : ∀ (k : ℕ) (x : D), (f^[k] x).1 = (cubicRounding b)^[k] x.1 := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        change cubicRounding b (f^[k] x).1 = _
        rw [ih]
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] start)
  have hordered : ∃ i j : ℕ, i < j ∧ f^[i] start = f^[j] start := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hordered
  let x : D := f^[i] start
  have hperiod : (cubicRounding b)^[j-i] x.1 = x.1 := by
    rw [← hval]
    change (f^[j-i] (f^[i] start)).1 = (f^[i] start).1
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hij), heq]
  have hL : 2 ≤ j-i := by
    have hn : 0 < j-i := Nat.sub_pos_of_lt hij
    by_contra h
    have h1 : j-i = 1 := by omega
    rw [h1, Function.iterate_one] at hperiod
    exact cubicRounding_no_fixed hb x.2 hperiod
  refine ⟨x.1, j-i, x.2, hL, hperiod, ?_⟩
  intro k
  exact cubicParityDomain_bounds hb (cubicRounding_iterate_mem hb ho x.2 k)

/-- A least-period formulation also certifies distinctness before return. -/
theorem cubicRounding_exists_primitive {b : ℕ} (hb : 3 ≤ b) (ho : b % 2 = 1) :
    ∃ x L : ℕ, cubicParityDomain b x ∧ 2 ≤ L ∧
      (cubicRounding b)^[L] x = x ∧
      (∀ i < L, ∀ j < L,
        (cubicRounding b)^[i] x = (cubicRounding b)^[j] x → i = j) ∧
      ∀ i j : ℕ, (cubicRounding b)^[j] x < ((cubicRounding b)^[i] x) ^ 3 := by
  obtain ⟨x, n, hx, hn, hp, hband⟩ := cubicRounding_exists_periodic hb ho
  have hperiod : Function.IsPeriodicPt (cubicRounding b) n x := hp
  have hpositive := hperiod.minimalPeriod_pos (by omega : 0 < n)
  have hnotone : Function.minimalPeriod (cubicRounding b) x ≠ 1 := by
    intro h
    exact cubicRounding_no_fixed hb hx
      (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
  refine ⟨x, Function.minimalPeriod (cubicRounding b) x, hx, by omega,
    Function.iterate_minimalPeriod, ?_, ?_⟩
  · intro i hi j hj hij
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hi hj).mp hij
  · intro i j
    exact lt_of_lt_of_le (hband j).2 (Nat.pow_le_pow_left (hband i).1 3)

/-- The shifted odd branch preserves the fixed point at one. -/
def branchOffset (x : ℕ) : ℕ :=
  if x = 1 then 1 else if x % 2 = 0 then floorPower x else floorPower x - 1

/-- All same-branch differences above one coincide, as integer differences. -/
theorem branchOffset_same_branch_difference {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2) :
    (branchOffset y : ℤ) - branchOffset x = (floorPower y : ℤ) - floorPower x := by
  have hxp := floorPower_pos (n := x) (by omega)
  have hyp := floorPower_pos (n := y) (by omega)
  have hx1 : x ≠ 1 := by omega
  have hy1 : y ≠ 1 := by omega
  unfold branchOffset
  simp only [if_neg hx1, if_neg hy1]
  split_ifs <;> omega

/-- The real branch value, using its integer radicand. -/
noncomputable def cubicBranchValue (x : ℕ) : ℝ :=
  Real.sqrt ((if x % 2 = 0 then x else x ^ 3 : ℕ) : ℝ)

theorem cubicBranchValue_unit_cell (x : ℕ) :
    (floorPower x : ℝ) ≤ cubicBranchValue x ∧
    cubicBranchValue x < (floorPower x : ℝ) + 1 := by
  let r := if x % 2 = 0 then x else x ^ 3
  have hJ : floorPower x = r.sqrt := by
    unfold floorPower r
    split_ifs <;> rfl
  change (floorPower x : ℝ) ≤ Real.sqrt (r : ℝ) ∧
    Real.sqrt (r : ℝ) < (floorPower x : ℝ) + 1
  rw [hJ]
  constructor
  · apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' r
  · apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.lt_succ_sqrt' r

theorem cubicRounding_real_loss (b x : ℕ) :
    0 ≤ cubicBranchValue x - cubicRounding b x ∧
    cubicBranchValue x - cubicRounding b x < 2 := by
  obtain ⟨hlo, hhi⟩ := cubicBranchValue_unit_cell x
  have hp : (cubicRounding b x : ℝ) ≤ floorPower x := by
    exact_mod_cast cubicParityProject_le b (floorPower x)
  have hq : (floorPower x : ℝ) ≤ cubicRounding b x + 1 := by
    exact_mod_cast cubicParityProject_loss b (floorPower x)
  constructor <;> linarith

/-- The strict smooth gap test survives the constant shift on a whole branch. -/
theorem branchOffset_same_branch_smooth_gap {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2) :
    |((branchOffset y : ℝ) - branchOffset x) -
      (cubicBranchValue y - cubicBranchValue x)| < 1 := by
  have hdiff : (branchOffset y : ℝ) - branchOffset x =
      (floorPower y : ℝ) - floorPower x := by
    exact_mod_cast branchOffset_same_branch_difference hx hy hp
  rw [hdiff]
  obtain ⟨hxlo, hxhi⟩ := cubicBranchValue_unit_cell x
  obtain ⟨hylo, hyhi⟩ := cubicBranchValue_unit_cell y
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Two even integers cannot both lie at distance strictly below one from a real number. -/
theorem even_integer_unique_within_one {k l : ℤ} {r : ℝ}
    (hk : k % 2 = 0) (hl : l % 2 = 0)
    (hkr : |(k : ℝ) - r| < 1) (hlr : |(l : ℝ) - r| < 1) : k = l := by
  obtain ⟨hklo, hkhi⟩ := abs_lt.mp hkr
  obtain ⟨hllo, hlhi⟩ := abs_lt.mp hlr
  have hu : (k : ℝ) - l < 2 := by linarith
  have hd : (-2 : ℝ) < (k : ℝ) - l := by linarith
  have hu' : k - l < 2 := by exact_mod_cast hu
  have hd' : -2 < k - l := by exact_mod_cast hd
  omega

/-- Whenever the shifted successors have equal parity, their gap passes the unique-even test. -/
theorem branchOffset_nearest_even_gap {x y : ℕ}
    (hx : 1 < x) (hy : 1 < y) (hp : x % 2 = y % 2)
    (hs : branchOffset x % 2 = branchOffset y % 2) :
    ∀ k : ℤ, k % 2 = 0 →
      |(k : ℝ) - (cubicBranchValue y - cubicBranchValue x)| < 1 →
      k = (branchOffset y : ℤ) - branchOffset x := by
  intro k hk hkr
  have he : ((branchOffset y : ℤ) - branchOffset x) % 2 = 0 := by omega
  apply even_integer_unique_within_one hk he hkr
  simpa only [Int.cast_sub, Int.cast_natCast] using
    branchOffset_same_branch_smooth_gap hx hy hp

/-- The literal shifted cycle, listed before its return. -/
def branchOffsetCycle : List ℕ := [13,45,300,17,69,572,23,109,1136,33,188]

theorem branchOffsetCycle_edges :
    branchOffsetCycle.map branchOffset = branchOffsetCycle.tail ++ [13] := by
  decide +kernel

theorem branchOffsetCycle_distinct : branchOffsetCycle.Nodup := by decide +kernel

theorem branchOffsetCycle_cells :
    branchOffsetCycle.map floorPower = [46,301,17,70,573,23,110,1137,33,189,13] := by
  decide +kernel

theorem branchOffsetCycle_rounding :
    branchOffsetCycle.map (cubicRounding 11) = branchOffsetCycle.tail ++ [13] := by
  decide +kernel

theorem branchOffsetCycle_bounds :
    ∀ x ∈ branchOffsetCycle, 13 ≤ x ∧ x ≤ 1136 ∧ cubicParityDomain 11 x := by
  unfold branchOffsetCycle cubicParityDomain
  decide +kernel

theorem branchOffsetCycle_counts :
    branchOffsetCycle.length = 11 ∧
    (branchOffsetCycle.filter (fun x => x % 2 = 1)).length = 7 ∧
    (branchOffsetCycle.filter (fun x => x % 2 = 0)).length = 4 ∧ 1136 < 13 ^ 3 := by
  decide +kernel

theorem branchOffsetCycle_iterate : branchOffset^[11] 13 = 13 := by decide +kernel

theorem branchOffsetCycle_iterates :
    (List.range 11).map (fun k => branchOffset^[k] 13) = branchOffsetCycle := by
  decide +kernel

theorem branchOffsetCycle_primitive :
    ∀ i j : Fin 11, branchOffset^[i.val] 13 = branchOffset^[j.val] 13 → i = j := by
  decide +kernel

theorem branchOffsetCycle_rank_rotation :
    [13,17,23,33,45,69,109,188,300,572,1136].map branchOffset =
    [45,69,109,188,300,572,1136,13,17,23,33] := by
  decide +kernel

theorem branchOffsetCycle_mechanical_prefix :
    ∀ k : Fin 12,
      ((branchOffsetCycle.take k.val).filter (fun x => x % 2 = 1)).length =
        (k.val * 7 + 10) / 11 := by
  decide +kernel

end Problems.Juggler
