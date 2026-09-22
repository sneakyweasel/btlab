import Problems.Juggler.CollatzBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Floor.Semifield

/-!
Exact construction and arithmetic for Paper E, Theorem 4.1.
The analytic assertion that the required simultaneous fractional-part boxes
are visited arbitrarily far out is a separate, unresolved dependency.
-/

namespace Problems.Juggler.PaperEModularReturn

noncomputable section

open CollatzBridge

theorem iterate_add_after (f : ℕ → ℕ) (a b n : ℕ) :
    f^[a+b] n = f^[b] (f^[a] n) := by
  rw [Nat.add_comm a b, Function.iterate_add_apply]

def runWord (a b : ℕ) : List Branch :=
  oddEvenBlock a b

@[simp] theorem runWord_length (a b : ℕ) : (runWord a b).length = a+b := by
  simp [runWord, oddEvenBlock]

@[simp] theorem runWord_oddCount (a b : ℕ) : oddCount (runWord a b) = a := by
  simp [runWord, oddEvenBlock, oddCount_append, oddCount_replicate_odd, oddCount_replicate_even]

theorem runWord_charge_add (a b : ℕ) : wordConst (runWord a b) + 2^a = 3^a := by
  induction a with
  | zero =>
    simp only [runWord, oddEvenBlock, List.replicate_zero, List.nil_append, pow_zero]
    have h := (wordConst_eq_zero_iff (List.replicate b .even)).mpr
      (oddCount_replicate_even b)
    omega
  | succ a ih =>
    rw [show runWord (a+1) b = .odd :: runWord a b by
      simp [runWord, oddEvenBlock, List.replicate_succ]]
    rw [wordConst_odd, runWord_oddCount, pow_succ, pow_succ]
    omega

theorem runWord_charge (a b : ℕ) : wordConst (runWord a b) = 3^a - 2^a := by
  have := runWord_charge_add a b
  omega

/-- Repeated integer roots give one exact power cell at every depth. -/
theorem le_sqrt_iterate (k N m : ℕ) :
    m ≤ Nat.sqrt^[k] N ↔ m^(2^k) ≤ N := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.le_sqrt, ih]
    rw [← pow_two, ← pow_mul, pow_succ']

theorem sqrt_iterate_cell (k N m : ℕ) :
    Nat.sqrt^[k] N = m ↔ m^(2^k) ≤ N ∧ N < (m+1)^(2^k) := by
  have h₁ := le_sqrt_iterate k N m
  have h₂ := le_sqrt_iterate k N (m+1)
  omega

/-- All of the initial perfect-power steps are genuine odd branches. -/
theorem odd_tower (s k : ℕ) (hs : s % 2 = 1) :
    follows (s^(2^k)) (List.replicate k .odd) ∧
    floorPower^[k] (s^(2^k)) = s^(3^k) := by
  induction k generalizing s with
  | zero => simp [follows]
  | succ k ih =>
    have hp : s^(2^(k+1)) % 2 = 1 := by simp [Nat.pow_mod, hs]
    have hstep : floorPower (s^(2^(k+1))) = (s^3)^(2^k) := by
      rw [floorPower_odd_eq hp]
      have he : (s^(2^(k+1)))^3 = ((s^3)^(2^k))^2 := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, pow_succ]
        congr 1
        ring
      rw [he, Nat.sqrt_eq']
    obtain ⟨hf, hi⟩ := ih (s^3) (by simp [Nat.pow_mod, hs])
    constructor
    · simpa [List.replicate_succ, follows, hp, hstep] using hf
    · rw [Function.iterate_succ_apply, hstep, hi]
      rw [← pow_mul, pow_succ']

/-- The last odd branch introduces exactly one square-root floor. -/
theorem odd_run (s k : ℕ) (hs : s % 2 = 1) :
    follows (s^(2^k)) (List.replicate (k+1) .odd) ∧
    floorPower^[k+1] (s^(2^k)) = Nat.sqrt (s^(3^(k+1))) := by
  obtain ⟨hf, hi⟩ := odd_tower s k hs
  have ho : s^(3^k) % 2 = 1 := by simp [Nat.pow_mod, hs]
  constructor
  · have h := follows_append hf (v := [.odd]) (by
      simp [image_eq_iterate, hi, follows, ho])
    simpa only [List.replicate_add, List.replicate_one] using h
  · rw [Function.iterate_succ_apply', hi, floorPower_odd_eq ho]
    rw [← pow_mul, pow_succ]

/-- An even run is precisely repeated integer square roots. -/
theorem even_run (N b : ℕ) (he : ∀ j < b, (Nat.sqrt^[j] N) % 2 = 0) :
    follows N (List.replicate b .even) ∧ floorPower^[b] N = Nat.sqrt^[b] N := by
  induction b generalizing N with
  | zero => simp [follows]
  | succ b ih =>
    have hN : N % 2 = 0 := by simpa using he 0 (by omega)
    obtain ⟨hf, hi⟩ := ih (Nat.sqrt N) (by
      intro j hj
      simpa [Function.iterate_succ_apply] using he (j+1) (by omega))
    constructor
    · simpa [List.replicate_succ, follows, hN, floorPower_even_eq hN] using hf
    · simpa [Function.iterate_succ_apply, floorPower_even_eq hN] using hi

/-- The integer root tower is the floor of the corresponding real power. -/
theorem sqrt_iterate_eq_floor (N k : ℕ) :
    Nat.sqrt^[k] N = ⌊(N : ℝ)^((2^k : ℝ)⁻¹)⌋₊ := by
  apply eq_of_forall_le_iff
  intro m
  rw [le_sqrt_iterate, Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)]
  have hp : (0 : ℝ) < 2^k := by positivity
  have he : ((N : ℝ)^((2^k : ℝ)⁻¹))^(2^k : ℝ) = N := by
    rw [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have h := Real.rpow_le_rpow_iff (x := (m : ℝ))
    (y := (N : ℝ)^((2^k : ℝ)⁻¹)) (by positivity) (by positivity) hp
  rw [he] at h
  rw [show (2^k : ℝ) = ((2^k : ℕ) : ℝ) by norm_cast,
    Real.rpow_natCast] at h
  exact_mod_cast h

theorem power_root_eq_floor (s a j : ℕ) :
    Nat.sqrt^[j+1] (s^(3^a)) = ⌊(s : ℝ)^((3^a : ℝ)/2^(j+1))⌋₊ := by
  rw [sqrt_iterate_eq_floor, Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  simp [div_eq_mul_inv]

/-- The fractional-part box selects exactly the requested integer residue. -/
theorem floor_mod_of_box {x : ℝ} (hx : 0 ≤ x) {m r : ℕ} (hm : 0 < m) (hr : r < m)
    (hlo : (r : ℝ)/m ≤ Int.fract (x/m))
    (hhi : Int.fract (x/m) < ((r : ℝ)+1)/m) : ⌊x⌋₊ % m = r := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxdiv : 0 ≤ x/(m : ℝ) := div_nonneg hx hmR.le
  have he : Int.fract (x/(m : ℝ))*(m : ℝ) =
      x - (⌊x⌋₊ / m : ℕ)*(m : ℝ) := by
    rw [Int.fract, ← natCast_floor_eq_intCast_floor hxdiv, Nat.floor_div_natCast]
    field_simp
  have hl := (div_le_iff₀ hmR).mp hlo
  have hh := (lt_div_iff₀ hmR).mp hhi
  rw [he] at hl hh
  have hf : ⌊x⌋₊ = (⌊x⌋₊/m)*m+r := by
    apply (Nat.floor_eq_iff hx).mpr
    push_cast
    constructor <;> linarith
  have hmod := congrArg (fun n : ℕ => n % m) hf
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr] using hmod

def powerValue (s a j : ℕ) : ℝ := (s : ℝ)^((3^a : ℝ)/2^(j+1))

/-- The particular positive box used in the paper, with coordinates reversed. -/
def ReturnBox (a b M t : ℕ) : Prop :=
  let s := 1+2*M*t
  (1 : ℝ)/(2*M) ≤ Int.fract (powerValue s a b/(2*M)) ∧
  Int.fract (powerValue s a b/(2*M)) < 2/(2*M) ∧
  ∀ j < b, Int.fract (powerValue s a j/2) < (1/2 : ℝ)

theorem box_guards {a b M t : ℕ} (hM : 0 < M) (h : ReturnBox a b M t) :
    (∀ j < b, (Nat.sqrt^[j+1] ((1+2*M*t)^(3^a))) % 2 = 0) ∧
    (Nat.sqrt^[b+1] ((1+2*M*t)^(3^a))) % (2*M) = 1 := by
  obtain ⟨hlo,hhi,he⟩ := h
  constructor
  · intro j hj
    rw [power_root_eq_floor]
    apply floor_mod_of_box (by positivity) (by norm_num) (by norm_num)
    · simp [Int.fract_nonneg]
    · simpa [powerValue] using he j hj
  · rw [power_root_eq_floor]
    apply floor_mod_of_box (by positivity) (by omega) (by omega)
    · simpa [powerValue] using hlo
    · simpa [powerValue, show (1 : ℝ)+1 = 2 by norm_num] using hhi

/-- The box supplies actual parity guards, not merely a prescribed symbolic word. -/
theorem actual_run {s k b : ℕ} (hs : s % 2 = 1)
    (he : ∀ j < b, (Nat.sqrt^[j+1] (s^(3^(k+1)))) % 2 = 0) :
    itinerary (s^(2^k)) (k+1+b) = runWord (k+1) b ∧
    floorPower^[k+1+b] (s^(2^k)) = Nat.sqrt^[b+1] (s^(3^(k+1))) := by
  obtain ⟨ho,hi⟩ := odd_run s k hs
  obtain ⟨hf,hj⟩ := even_run (Nat.sqrt (s^(3^(k+1)))) b (by
    intro j hj
    simpa [Function.iterate_succ_apply] using he j hj)
  constructor
  · rw [← runWord_length (k+1) b]
    apply (follows_iff_itinerary _ _).mp
    apply follows_append ho
    simpa [image_eq_iterate, hi] using hf
  · rw [iterate_add_after, hi, hj, Function.iterate_succ_apply]

/-- A completely explicit size threshold makes the endpoint exceed the start. -/
theorem root_endpoint_gt {s e p d : ℕ} (hs : 2^(2^d) ≤ s)
    (hex : e*2^d < p) : s^e < Nat.sqrt^[d] (s^p) := by
  have hs1 : 1 ≤ s := le_trans (Nat.one_le_pow _ 2 (by omega)) hs
  have he1 : 1 ≤ s^e := Nat.one_le_pow e s hs1
  have hcell : (s^e+1)^(2^d) ≤ s^p := calc
    (s^e+1)^(2^d) ≤ (2*s^e)^(2^d) :=
      Nat.pow_le_pow_left (by omega) _
    _ = 2^(2^d)*s^(e*2^d) := by rw [mul_pow, ← pow_mul]
    _ ≤ s*s^(e*2^d) := Nat.mul_le_mul_right _ hs
    _ = s^(e*2^d+1) := by rw [pow_succ, mul_comm]
    _ ≤ s^p := Nat.pow_le_pow_right (by omega) (by omega)
  have h := (le_sqrt_iterate d (s^p) (s^e+1)).mpr hcell
  omega

theorem odd_prefix_above {n a : ℕ} (h : follows n (List.replicate a .odd)) :
    ∀ j ≤ a, n ≤ floorPower^[j] n := by
  induction a generalizing n with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst j
    simp
  | succ a ih =>
    have hodd : n % 2 = 1 := h.1
    have hn : 1 ≤ n := by omega
    have hstep : n ≤ floorPower n := by
      rw [floorPower_odd_eq hodd, Nat.le_sqrt']
      exact Nat.pow_le_pow_right (by omega) (by omega)
    intro j hj
    cases j with
    | zero => simp
    | succ j =>
      rw [Function.iterate_succ_apply]
      exact le_trans hstep (ih h.2 j (by omega))

theorem even_prefix_above_endpoint {n b : ℕ} (h : follows n (List.replicate b .even)) :
    ∀ j ≤ b, floorPower^[b] n ≤ floorPower^[j] n := by
  induction b generalizing n with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst j
    simp
  | succ b ih =>
    have heven : n % 2 = 0 := h.1
    have hstep : floorPower n ≤ n := by
      rw [floorPower_even_eq heven]; exact Nat.sqrt_le_self n
    intro j hj
    cases j with
    | zero =>
      rw [Function.iterate_succ_apply]
      exact le_trans (by simpa using ih h.2 0 (by omega)) hstep
    | succ j =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih h.2 j (by omega)

theorem run_above_start {n a b : ℕ} (h : itinerary n (a+b) = runWord a b)
    (hend : n ≤ floorPower^[a+b] n) : ∀ j ≤ a+b, n ≤ floorPower^[j] n := by
  have hf : follows n (runWord a b) :=
    (follows_iff_itinerary _ _).mpr (by simpa using h)
  have ho := follows_of_append_left hf
  have he := follows_of_append_right hf
  have he' : follows (floorPower^[a] n) (List.replicate b .even) := by
    simpa [image_eq_iterate] using he
  intro j hj
  by_cases hja : j ≤ a
  · exact odd_prefix_above ho j hja
  · have hjab : j-a ≤ b := by omega
    have hjdecomp : a+(j-a) = j := by omega
    have h := even_prefix_above_endpoint he' (j-a) hjab
    rw [← iterate_add_after, ← iterate_add_after, hjdecomp] at h
    exact le_trans hend h

/-- The orbit part of Theorem 4.1 for every sufficiently large box visit. -/
theorem modular_return_of_box {k b M t : ℕ} (hM : 0 < M)
    (hex : 2^(k+1+b) < 3^(k+1))
    (hsize : 2^(2^(b+1)) ≤ 1+2*M*t) (hbox : ReturnBox (k+1) b M t) :
    let n := (1+2*M*t)^(2^k)
    n % 2 = 1 ∧ itinerary n (k+1+b) = runWord (k+1) b ∧
    (∀ j ≤ k+1+b, n ≤ floorPower^[j] n) ∧ n < floorPower^[k+1+b] n ∧
    n % (2*M) = 1 ∧ (floorPower^[k+1+b] n) % (2*M) = 1 := by
  have hs : (1+2*M*t) % 2 = 1 := by simp [Nat.add_mod, Nat.mul_mod]
  have hsM : (1+2*M*t) % (2*M) = 1 := by
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨he, hm⟩ := box_guards hM hbox
  obtain ⟨hi,hend⟩ := actual_run hs he
  have hex' : 2^k*2^(b+1) < 3^(k+1) := by
    rw [← pow_add, show k+(b+1) = k+1+b by omega]
    exact hex
  have hgt := root_endpoint_gt hsize hex'
  rw [← hend] at hgt
  refine ⟨by simp [Nat.pow_mod, hs], hi, run_above_start hi hgt.le, hgt, ?_, ?_⟩
  · simp [Nat.pow_mod, hsM, Nat.mod_eq_of_lt (show 1 < 2*M by omega)]
  · rwa [hend]

/-- All orbit conclusions of (4.1), with no reference to a symbolic code. -/
def ModularReturn (a b M n : ℕ) : Prop :=
  n % 2 = 1 ∧ itinerary n (a+b) = runWord a b ∧
  (∀ j ≤ a+b, n ≤ floorPower^[j] n) ∧ n < floorPower^[a+b] n ∧
  n % (2*M) = 1 ∧ (floorPower^[a+b] n) % (2*M) = 1

/-- The remaining analytic proposition. It asserts joint visits, not separate
coordinate density, and is not proved in this module. -/
def BoxRecurrence (a b M : ℕ) : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, T ≤ t ∧ ReturnBox a b M t

/-- Exact reduction of infinitude to the outstanding analytic proposition. -/
theorem infinite_modular_returns_of_box_recurrence {a b M : ℕ}
    (ha : 0 < a) (hM : 0 < M) (hex : 2^(a+b) < 3^a)
    (hrec : BoxRecurrence a b M) (B : ℕ) :
    {n : ℕ | B < n ∧ ModularReturn a b M n}.Infinite := by
  cases a with
  | zero => omega
  | succ k =>
    apply Set.infinite_iff_exists_gt.mpr
    intro C
    obtain ⟨t, ht, hbox⟩ := hrec (max (2^(2^(b+1))) (max (B+1) (C+1)))
    have htB : B < t := by omega
    have htC : C < t := by omega
    have htS : 2^(2^(b+1)) ≤ t := by omega
    have hts : t ≤ 1+2*M*t := by nlinarith
    have hsn : 1+2*M*t ≤ (1+2*M*t)^(2^k) := Nat.le_self_pow (by positivity) _
    have hreturn := modular_return_of_box hM hex (le_trans htS hts) hbox
    refine ⟨(1+2*M*t)^(2^k), ?_, lt_of_lt_of_le htC (le_trans hts hsn)⟩
    exact ⟨lt_of_lt_of_le htB (le_trans hts hsn), hreturn⟩

def runCode (a b : ℕ) : ℚ :=
  (wordConst (runWord a b) : ℚ) / (3^a - 2^(a+b) : ℕ)

/-- Exact gcd cancellation; this uses the actual word charge. -/
theorem runWord_gcd (a b : ℕ) (ha : 0 < a) (hex : 2^(a+b) < 3^a) :
    Nat.gcd (3^a - 2^(a+b)) (wordConst (runWord a b)) =
      Nat.gcd (3^a-2^a) (2^b-1) := by
  have h₂ : 2^a ≤ 2^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  have h₃ : 2^a ≤ 3^a := le_trans h₂ hex.le
  have hA : 3^a-2^a+2^a = 3^a := Nat.sub_add_cancel h₃
  have hD : 3^a-2^(a+b)+2^(a+b) = 3^a := Nat.sub_add_cancel hex.le
  have hle : 3^a-2^(a+b) ≤ 3^a-2^a := by omega
  have hdiff : (3^a-2^a)-(3^a-2^(a+b)) = 2^a*(2^b-1) := by
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    have he := Nat.sub_add_cancel hp
    rw [pow_add] at h₂ hD ⊢
    have hsub := Nat.sub_add_cancel hle
    rw [pow_add] at hsub
    have hmul := congrArg (fun x : ℕ => 2^a*x) he
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hcop : Nat.Coprime (3^a-2^a) (2^a) := by
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    apply Nat.odd_iff.mpr
    have hpow₂ : 2^a % 2 = 0 := by simp [Nat.pow_mod, Nat.ne_of_gt ha]
    have hpow₃ : 3^a % 2 = 1 := by simp [Nat.pow_mod]
    omega
  rw [runWord_charge, Nat.gcd_comm,
    ← Nat.gcd_self_sub_right hle, hdiff]
  exact hcop.symm.gcd_mul_left_cancel_right (2^b-1)

/-- Formula (4.2) is the reduced denominator of the rational periodic-word code. -/
theorem runCode_den (a b : ℕ) (ha : 0 < a) (hex : 2^(a+b) < 3^a) :
    (runCode a b).den = (3^a-2^(a+b)) / Nat.gcd (3^a-2^a) (2^b-1) := by
  have hD : 3^a-2^(a+b) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hex)
  unfold runCode
  rw [← Int.cast_natCast (wordConst _), ← Rat.mkRat_eq_div, Rat.den_mkRat]
  simp only [hD, if_false, Int.natAbs_natCast]
  rw [runWord_gcd a b ha hex]

/-- An elementary Bernoulli bound suffices for denominator growth. -/
theorem bernoulli_three_two (a : ℕ) : (a+2)*2^a ≤ 2*3^a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.zero_le (a*2^a)]

/-- Every sufficiently large odd-run length has denominator above the given bound. -/
theorem runCode_den_gt (b B a : ℕ) (hb : 0 < b)
    (ha : 2*(2^b+(B+1)*(2^b-1)) ≤ a) :
    2^(a+b) < 3^a ∧ B < (runCode a b).den := by
  have hc : 0 < 2^b-1 := by
    have := Nat.one_lt_pow (Nat.ne_of_gt hb) (by norm_num : 1 < 2)
    omega
  have hp : 0 < 2^a := by positivity
  have hbern := bernoulli_three_two a
  have hlower : (B+1)*(2^b-1) < 3^a-2^(a+b) := by
    rw [pow_add]
    have hmul := Nat.mul_le_mul_right (2^a) ha
    have hpos : (B+1)*(2^b-1) ≤ (B+1)*(2^b-1)*2^a :=
      Nat.le_mul_of_pos_right _ hp
    have hstrict : (B+1)*(2^b-1) + 2^a*2^b < 3^a := by nlinarith
    omega
  have hex : 2^(a+b) < 3^a := by omega
  refine ⟨hex, ?_⟩
  have ha0 : 0 < a := by have := Nat.one_le_pow b 2 (by omega); omega
  rw [runCode_den a b ha0 hex]
  have hg : 0 < Nat.gcd (3^a-2^a) (2^b-1) := Nat.gcd_pos_of_pos_right _ hc
  have hg_le := Nat.gcd_le_right (3^a-2^a) hc
  have hmul := Nat.mul_le_mul_left (B+1) hg_le
  have hdiv := (Nat.le_div_iff_mul_le hg).mpr (le_trans hmul hlower.le)
  omega

theorem runCode_den_unbounded (b : ℕ) (hb : 0 < b) :
    ∀ B : ℕ, ∃ a : ℕ, 0 < a ∧ 2^(a+b) < 3^a ∧ B < (runCode a b).den := by
  intro B
  refine ⟨2*(2^b+(B+1)*(2^b-1)), by positivity, ?_⟩
  exact runCode_den_gt b B _ hb le_rfl

/-- Complete assembly, conditional on the explicitly named analytic input.
This is not an unconditional formalization of Theorem 4.1. -/
theorem theorem41_of_box_recurrence {a b M : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hex : 2^(a+b) < 3^a)
    (hrec : BoxRecurrence a b M) :
    (∀ B : ℕ, {n : ℕ | B < n ∧ ModularReturn a b M n}.Infinite) ∧
    (runCode a b).den = (3^a-2^(a+b)) / Nat.gcd (3^a-2^a) (2^b-1) ∧
    (∀ Q : ℕ, ∃ A : ℕ, 0 < A ∧ 2^(A+b) < 3^A ∧ Q < (runCode A b).den) :=
  ⟨infinite_modular_returns_of_box_recurrence ha hM hex hrec,
    runCode_den a b ha hex, runCode_den_unbounded b hb⟩

end

end Problems.Juggler.PaperEModularReturn
