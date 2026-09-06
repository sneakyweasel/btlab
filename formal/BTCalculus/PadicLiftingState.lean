import BTCalculus.PadicLifting

/-!
# Minimal finite-horizon state for 3-adic lifting

Three statements about how much of a residual state the next levels of the
lifting tree actually see.

1. **Unit scaling.** On a surviving branch, where `lsdZ (eval a f) = 0`,
   the section derivative is linear in the state: `𝔇_a (λ f) = λ 𝔇_a f`.
   For `λ` coprime to 3 survival itself is `λ`-invariant, so a word
   survives for `f` exactly when it survives for `λ f`. Since a word
   carries its own trits, that is invariance of the whole ordered
   trit-labelled subtree, and it shows the Newton jet `Φ_r` is not the
   minimal state — it changes under scaling while the subtree does not.

2. **The linear transition law.** `𝔇_a (c + b x) = D(c + ab) + b x`, so
   linear states are closed under the section operators and `b` is
   invariant along the whole tree.

3. **The nonsingular path.** For `b` coprime to 3 the lifting path of
   `c + b x` is the unique trit word of its length, given explicitly by
   iterating the Hensel trit `lsdZ (-(c b))`. That trit is the balanced
   digit of the Newton correction `-c/b`, since `b` is its own inverse
   modulo 3.

4. **The block shift.** A branch whose derivative valuation is at least
   `|w|` is fully ternary along `w`, and the state it reaches is shifted by
   `packWord w`, the balanced value of the word — not by its digit sum.
   Since `packWord` is injective on words of a fixed length `e`, those
   shifts form a complete residue system modulo `3 ^ e`, so exactly one
   leaf of the block continues into the next one. That is the algebraic
   fact the singular count rests on.

The counting classification built on these is not formalised: it is a
finite exhaustive computation together with an induction on the horizon,
recorded in `docs/theory/lifting_state_complexity.md`.
-/

noncomputable section

namespace BTCalculus

open Polynomial

/-! ## Vanishing residues -/

/-- A residue trit vanishes exactly when the value is divisible by 3. -/
theorem lsdZ_eq_zero_iff (n : ℤ) : lsdZ n = 0 ↔ (3 : ℤ) ∣ n := by
  constructor
  · intro h
    have hm := lsdZ_mod n
    rw [h] at hm
    exact Int.modEq_zero_iff_dvd.mp hm
  · intro h
    exact lsdZ_unique (Or.inr (Or.inl rfl)) (Int.modEq_zero_iff_dvd.mpr h)

/-! ## Unit scaling on a surviving branch -/

/-- **Target 1.** On a surviving branch the section derivative is linear
in the state. The hypothesis is essential: off the tree the subtracted
residue is not `λ ρ_a(f)`. -/
theorem sectionDeriv_smul_of_root {a : ℤ} {f : ℤ[X]} (lam : ℤ)
    (h : lsdZ (eval a f) = 0) :
    sectionDeriv a (C lam * f) = C lam * sectionDeriv a f := by
  have hdvd : (3 : ℤ) ∣ eval a f := (lsdZ_eq_zero_iff _).mp h
  have hscaled : lsdZ (eval a (C lam * f)) = 0 := by
    refine (lsdZ_eq_zero_iff _).mpr ?_
    simpa [eval_mul, eval_C] using hdvd.mul_left lam
  refine Polynomial.funext (fun x => ?_)
  have hf := section_reconstruction_eval f a x
  have hg := section_reconstruction_eval (C lam * f) a x
  rw [h] at hf
  rw [hscaled] at hg
  have hmul : eval (a + 3 * x) (C lam * f) = lam * eval (a + 3 * x) f := by
    simp [eval_mul, eval_C]
  have hkey : (3 : ℤ) * eval x (sectionDeriv a (C lam * f))
      = 3 * (lam * eval x (sectionDeriv a f)) := by
    have h1 : (0 : ℤ) + 3 * eval x (sectionDeriv a (C lam * f))
        = lam * (0 + 3 * eval x (sectionDeriv a f)) := by
      rw [← hg, hmul, hf]
    linarith [h1]
  have hL := mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) hkey
  rw [hL]
  simp [eval_mul, eval_C]

/-- For `λ` coprime to 3, survival of a trit is unchanged by scaling. -/
theorem root_smul_iff {a lam : ℤ} {f : ℤ[X]} (hlam : ¬ (3 : ℤ) ∣ lam) :
    lsdZ (eval a (C lam * f)) = 0 ↔ lsdZ (eval a f) = 0 := by
  rw [lsdZ_eq_zero_iff, lsdZ_eq_zero_iff]
  simp only [eval_mul, eval_C]
  constructor
  · intro h
    rcases Int.prime_three.dvd_or_dvd h with h1 | h2
    · exact absurd h1 hlam
    · exact h2
  · intro h
    exact h.mul_left lam

/-- Along a surviving word the residual scales by the same unit. -/
theorem residualAlong_smul_of_outputs_zero (lam : ℤ) :
    ∀ (w : List ℤ) (f : ℤ[X]),
      outputAlong w f = List.replicate w.length 0 →
      residualAlong w (C lam * f) = C lam * residualAlong w f
  | [], f, _ => by simp [residualAlong]
  | a :: w, f, h => by
    have hlen : (a :: w).length = w.length + 1 := rfl
    rw [outputAlong_cons, hlen, List.replicate_succ, List.cons.injEq] at h
    have hsd : sectionDeriv a (C lam * f) = C lam * sectionDeriv a f :=
      sectionDeriv_smul_of_root lam h.1
    rw [residualAlong_cons, residualAlong_cons, hsd]
    exact residualAlong_smul_of_outputs_zero lam w (sectionDeriv a f) h.2

/-- **Target 1, word form.** For `λ` coprime to 3 a word survives for `f`
exactly when it survives for `λ f`. A word carries its own trits, so this
is invariance of the entire ordered trit-labelled lifting subtree — and
therefore `Φ_r`, which does change under scaling, is not minimal. -/
theorem outputAlong_smul_iff (lam : ℤ) (hlam : ¬ (3 : ℤ) ∣ lam) :
    ∀ (w : List ℤ) (f : ℤ[X]),
      outputAlong w (C lam * f) = List.replicate w.length 0 ↔
        outputAlong w f = List.replicate w.length 0
  | [], _ => by simp [outputAlong]
  | a :: w, f => by
    have hlen : (a :: w).length = w.length + 1 := rfl
    rw [outputAlong_cons, outputAlong_cons, hlen, List.replicate_succ,
      List.cons.injEq, List.cons.injEq]
    constructor
    · rintro ⟨hhead, htail⟩
      have hf0 : lsdZ (eval a f) = 0 := (root_smul_iff hlam).mp hhead
      rw [sectionDeriv_smul_of_root lam hf0] at htail
      exact ⟨hf0, (outputAlong_smul_iff lam hlam w (sectionDeriv a f)).mp htail⟩
    · rintro ⟨hhead, htail⟩
      refine ⟨(root_smul_iff hlam).mpr hhead, ?_⟩
      rw [sectionDeriv_smul_of_root lam hhead]
      exact (outputAlong_smul_iff lam hlam w (sectionDeriv a f)).mpr htail

/-- The lifting tree of a scaled polynomial is the same tree. -/
theorem isRootMod_smul_iff {lam : ℤ} (hlam : ¬ (3 : ℤ) ∣ lam) (w : List ℤ)
    (f : ℤ[X]) :
    IsRootMod w.length (C lam * f) (packWord w) ↔
      IsRootMod w.length f (packWord w) := by
  rw [lift_iff_outputs_zero, lift_iff_outputs_zero]
  exact outputAlong_smul_iff lam hlam w f

/-! ## The linear state -/

/-- The deep-regime residual state `c + b x`. -/
def linState (c b : ℤ) : ℤ[X] := C c + C b * X

/-- `eval x (linState c b) = c + b * x`. -/
theorem eval_linState (c b x : ℤ) : eval x (linState c b) = c + b * x := by
  simp [linState]

/-- **Target 2.** The transition law on linear states. The derivative `b`
does not move, so it is invariant along the whole lifting tree. -/
theorem sectionDeriv_linState (c b a : ℤ) :
    sectionDeriv a (linState c b) = linState (DZ (c + a * b)) b := by
  refine Polynomial.funext (fun x => ?_)
  have hrec := section_reconstruction_eval (linState c b) a x
  rw [eval_linState, eval_linState] at hrec
  have hcomm : c + b * a = c + a * b := by ring
  rw [hcomm] at hrec
  have hd : c + a * b = lsdZ (c + a * b) + 3 * DZ (c + a * b) := decomp _
  have hR := eval_linState (DZ (c + a * b)) b x
  linarith [hrec, hd, hR]

/-- A trit survives at a linear state exactly when `3 ∣ c + ab`. -/
theorem linState_root_iff (c b a : ℤ) :
    lsdZ (eval a (linState c b)) = 0 ↔ (3 : ℤ) ∣ c + a * b := by
  rw [eval_linState, lsdZ_eq_zero_iff]
  constructor
  · intro h
    have : c + a * b = c + b * a := by ring
    rw [this]
    exact h
  · intro h
    have : c + b * a = c + a * b := by ring
    rw [this]
    exact h

/-! ## The nonsingular lifting path -/

/-- The Hensel trit at a nonsingular linear state. -/
def henselTrit (c b : ℤ) : ℤ := lsdZ (-(c * b))

/-- The Hensel trit is a trit. -/
theorem henselTrit_isTrit (c b : ℤ) : isTrit (henselTrit c b) :=
  lsdZ_is_trit _

/-- The `r`-step lifting path of a nonsingular linear state. -/
def liftPath : ℕ → ℤ → ℤ → List ℤ
  | 0, _, _ => []
  | r + 1, c, b => henselTrit c b :: liftPath r (DZ (c + henselTrit c b * b)) b

/-- `liftPath r c b` has length `r`. -/
theorem liftPath_length : ∀ (r : ℕ) (c b : ℤ), (liftPath r c b).length = r
  | 0, _, _ => rfl
  | r + 1, c, b => by
    rw [liftPath, List.length_cons, liftPath_length r _ b]

/-- When `3` does not divide `b`, the Hensel trit solves `3 | c + t * b`. -/
theorem henselTrit_dvd {b : ℤ} (hb : ¬ (3 : ℤ) ∣ b) (c : ℤ) :
    (3 : ℤ) ∣ c + henselTrit c b * b := by
  have h := dvd_add_mul_lsdZ (b := b) (c := c) hb
  have hcomm : c + b * lsdZ (-(c * b)) = c + henselTrit c b * b := by
    unfold henselTrit; ring
  rwa [hcomm] at h

/-- **Target 3a.** The path really lifts: every output trit along it
vanishes, to any depth. -/
theorem outputAlong_liftPath {b : ℤ} (hb : ¬ (3 : ℤ) ∣ b) :
    ∀ (r : ℕ) (c : ℤ),
      outputAlong (liftPath r c b) (linState c b) = List.replicate r 0
  | 0, _ => by simp [liftPath, outputAlong]
  | r + 1, c => by
    have hhead : lsdZ (eval (henselTrit c b) (linState c b)) = 0 :=
      (linState_root_iff c b _).mpr (henselTrit_dvd hb c)
    rw [liftPath, outputAlong_cons, hhead, List.replicate_succ,
      sectionDeriv_linState]
    rw [outputAlong_liftPath hb r (DZ (c + henselTrit c b * b))]

/-- **Target 3b.** The path is the only trit word of its length that
lifts, so at a nonsingular state the depth-`r` subtree is a single path. -/
theorem liftPath_unique {b : ℤ} (hb : ¬ (3 : ℤ) ∣ b) :
    ∀ (w : List ℤ) (c : ℤ), isTritList w →
      outputAlong w (linState c b) = List.replicate w.length 0 →
      w = liftPath w.length c b
  | [], _, _, _ => rfl
  | a :: w, c, hw, h => by
    have hlen : (a :: w).length = w.length + 1 := rfl
    rw [outputAlong_cons, hlen, List.replicate_succ, List.cons.injEq] at h
    have hda : (3 : ℤ) ∣ c + b * a := by
      have := (linState_root_iff c b a).mp h.1
      have hcomm : c + a * b = c + b * a := by ring
      rwa [hcomm] at this
    have hdh : (3 : ℤ) ∣ c + b * henselTrit c b := by
      have := henselTrit_dvd hb c
      have hcomm : c + henselTrit c b * b = c + b * henselTrit c b := by ring
      rwa [hcomm] at this
    have hae : a = henselTrit c b :=
      trit_unique_of_dvd hb hw.1 (henselTrit_isTrit c b) hda hdh
    subst hae
    rw [hlen, liftPath]
    refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
    rw [sectionDeriv_linState] at h
    exact liftPath_unique hb w (DZ (c + henselTrit c b * b)) hw.2 h.2

/-- **Target 3c.** The Hensel trit is the balanced digit of the Newton
correction: `b` is its own inverse modulo 3, so `lsdZ (-(c b))` is
`lsdZ (-(c/b))` for any inverse of `b`. This is the sense in which the
nonsingular half of the classification is Newton's method in balanced
digits, and nothing more. -/
theorem henselTrit_eq_newton {b c v : ℤ} (hb : ¬ (3 : ℤ) ∣ b)
    (hv : b * v ≡ 1 [ZMOD 3]) : henselTrit c b = lsdZ (-(c * v)) := by
  have hsq := sq_modEq_one_of_not_dvd hb
  have hvb : v ≡ b [ZMOD 3] := by
    calc v = v * 1 := by ring
      _ ≡ v * (b * b) [ZMOD 3] := (Int.ModEq.refl v).mul hsq.symm
      _ = (b * v) * b := by ring
      _ ≡ 1 * b [ZMOD 3] := hv.mul (Int.ModEq.refl b)
      _ = b := by ring
  have hmod : -(c * b) ≡ lsdZ (-(c * v)) [ZMOD 3] := by
    refine Int.ModEq.trans ?_ (lsdZ_mod (-(c * v)))
    exact ((Int.ModEq.refl c).mul hvb.symm).neg
  unfold henselTrit
  exact lsdZ_unique (lsdZ_is_trit _) hmod

/-! ## The singular block shift -/

/-- `D (3n) = n`. -/
theorem DZ_three_mul (n : ℤ) : DZ (3 * n) = n := by
  have hzero : DZ 0 = 0 := by decide
  have h : DZ (0 + 3 * n) = DZ 0 + n := DZ_add_mul3 0 n
  rw [hzero] at h
  simpa using h

/-- The reindexing that drives the block shift: dividing the state of a
singular branch by 3 turns the exponent `i` into `i + 1`. -/
theorem linState_block_step (j i : ℕ) (d a : ℤ) :
    sectionDeriv a (linState (3 ^ (j + 1) * d) (3 ^ (j + 1 + i)))
      = linState (3 ^ j * (d + 3 ^ i * a)) (3 ^ (j + (i + 1))) := by
  rw [sectionDeriv_linState]
  have hexp : j + 1 + i = j + (i + 1) := by omega
  have harg : 3 ^ (j + 1) * d + a * 3 ^ (j + 1 + i)
      = 3 * (3 ^ j * (d + 3 ^ i * a)) := by
    rw [hexp]
    ring
  rw [harg, DZ_three_mul, hexp]

/-- **Target 4.** The block shift law. A singular branch with derivative
valuation at least `w.length` is fully ternary along `w`, and the state it
reaches is shifted by the *balanced value* of the word, scaled by the
excess `3 ^ i`:

    𝔇_w (3^j d + 3^(j+i) x) = (d + 3^i · packWord w) + 3^(j+i) x,  j = |w|.

At `i = 0` this is the leaf law: the `3 ^ e` words of length `e` reach the
states `d + packWord w`, and `packWord` is injective on words of a fixed
length, so those shifts run over a complete residue system modulo `3 ^ e`.
That is what makes the shifted family separate residues; note the shift is
the balanced value of the word and not its digit sum. -/
theorem residualAlong_linState_pow :
    ∀ (w : List ℤ) (i : ℕ) (d : ℤ),
      residualAlong w (linState (3 ^ w.length * d) (3 ^ (w.length + i)))
        = linState (d + 3 ^ i * packWord w) (3 ^ (w.length + i))
  | [], i, d => by simp [residualAlong, packWord_nil]
  | a :: w, i, d => by
    have hlen : (a :: w).length = w.length + 1 := rfl
    rw [hlen, residualAlong_cons, linState_block_step,
      residualAlong_linState_pow w (i + 1) (d + 3 ^ i * a)]
    have hexp : w.length + 1 + i = w.length + (i + 1) := by omega
    have hshift : d + 3 ^ i * a + 3 ^ (i + 1) * packWord w
        = d + 3 ^ i * packWord (a :: w) := by
      rw [packWord_cons, pow_succ]
      ring
    rw [hexp, hshift]

/-- The leaf law at `i = 0`, the case the counting argument uses. -/
theorem residualAlong_linState_leaf (w : List ℤ) (d : ℤ) :
    residualAlong w (linState (3 ^ w.length * d) (3 ^ w.length))
      = linState (d + packWord w) (3 ^ w.length) := by
  have h := residualAlong_linState_pow w 0 d
  simpa using h

/-- **Target 4b.** Every word of length at most the derivative valuation
survives, so the first `e` levels of a singular branch are fully ternary
and the block really does have `3 ^ e` leaves. -/
theorem outputAlong_linState_pow :
    ∀ (w : List ℤ) (i : ℕ) (d : ℤ),
      outputAlong w (linState (3 ^ w.length * d) (3 ^ (w.length + i)))
        = List.replicate w.length 0
  | [], _, _ => rfl
  | a :: w, i, d => by
    have hlen : (a :: w).length = w.length + 1 := rfl
    rw [hlen, outputAlong_cons, List.replicate_succ, linState_block_step]
    refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
    · refine (linState_root_iff _ _ a).mpr ?_
      exact ⟨3 ^ w.length * d + a * 3 ^ (w.length + i), by rw [pow_succ, pow_add]; ring⟩
    · have hexp : w.length + (i + 1) = w.length + 1 + i := by omega
      have h := outputAlong_linState_pow w (i + 1) (d + 3 ^ i * a)
      simpa [hexp] using h

end BTCalculus
