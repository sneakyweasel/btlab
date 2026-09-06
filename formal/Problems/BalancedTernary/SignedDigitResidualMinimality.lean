import BTCalculus.NormalizedDerivative
import Problems.BalancedTernary.SignedDigitResidual

namespace Problems.BalancedTernary

open BTCalculus

/-!
Behavioral rigidity of ``F_{λ,U}(s,u)=λ · DZ(s+u)`` with output ``lsd(s+u)``.
This file does not repeat the finite/infinite phase law or the ``U_m`` fill.
-/

def signedTrace (gain s : ℤ) : List ℤ → List ℤ
  | [] => []
  | u :: rest => signedOut s u :: signedTrace gain (signedNext gain s u) rest

theorem signedTrace_nil (gain s : ℤ) : signedTrace gain s [] = [] :=
  rfl

theorem signedTrace_cons (gain s u : ℤ) (rest : List ℤ) :
    signedTrace gain s (u :: rest) =
      signedOut s u :: signedTrace gain (signedNext gain s u) rest :=
  rfl

theorem add_cancel_cong (s t u : ℤ) :
    s + u ≡ t + u [ZMOD 3] ↔ s ≡ t [ZMOD 3] := by
  constructor
  · intro h
    have hdvd : (3 : ℤ) ∣ (t + u) - (s + u) := Int.modEq_iff_dvd.mp h
    have hdiff : (t + u) - (s + u) = t - s := by ring
    exact Int.modEq_iff_dvd.mpr (by simpa [hdiff] using hdvd)
  · intro h
    have hdvd : (3 : ℤ) ∣ t - s := Int.modEq_iff_dvd.mp h
    have hdiff : (t + u) - (s + u) = t - s := by ring
    exact Int.modEq_iff_dvd.mpr (by simpa [hdiff] using hdvd)

theorem signedOut_eq_iff_cong (s t u : ℤ) :
    signedOut s u = signedOut t u ↔ s ≡ t [ZMOD 3] := by
  constructor
  · intro h
    have hlsd : lsdZ (s + u) = lsdZ (t + u) := by simpa [signedOut] using h
    have hsum : s + u ≡ t + u [ZMOD 3] :=
      (lsdZ_mod (s + u)).trans (hlsd ▸ (lsdZ_mod (t + u)).symm)
    exact (add_cancel_cong s t u).mp hsum
  · intro h
    have hsum : s + u ≡ t + u [ZMOD 3] := (add_cancel_cong s t u).mpr h
    exact trit_mod_unique (lsdZ_is_trit (s + u)) (lsdZ_is_trit (t + u))
      ((lsdZ_mod (s + u)).symm.trans (hsum.trans (lsdZ_mod (t + u))))

theorem signedOut_ne_of_not_cong {s t u : ℤ} (h : ¬ s ≡ t [ZMOD 3]) :
    signedOut s u ≠ signedOut t u :=
  mt (signedOut_eq_iff_cong s t u).mp h

theorem cong_iff_dvd_sub (s t : ℤ) :
    s ≡ t [ZMOD 3] ↔ (3 : ℤ) ∣ s - t := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have hneg : t - s = -(s - t) := by ring
    rw [hneg] at h
    exact (dvd_neg.mp h)
  · intro h
    have hneg : t - s = -(s - t) := by ring
    rw [hneg]
    exact dvd_neg.mpr h

theorem signedNext_diff_of_cong {s t : ℤ} (h : s ≡ t [ZMOD 3]) (gain u : ℤ) :
    signedNext gain s u =
      signedNext gain t u + gain * ((s - t) / 3) := by
  have hdvd : (3 : ℤ) ∣ s - t := (cong_iff_dvd_sub s t).mp h
  obtain ⟨k, hk⟩ := hdvd
  have harg : s + u = t + u + 3 * k := by linarith
  have hdiv : (s - t) / 3 = k := by
    rw [hk, Int.mul_ediv_cancel_left k (by decide : (3 : ℤ) ≠ 0)]
  rw [signedNext, signedNext, harg, DZ_add_mul3, hdiv]
  ring

def natVal3 (n : ℕ) : ℕ :=
  if h : 0 < n ∧ 3 ∣ n then
    have : n / 3 < n := Nat.div_lt_self h.1 (by decide : 1 < 3)
    natVal3 (n / 3) + 1
  else 0
termination_by n

def intVal3 (n : ℤ) : ℕ :=
  natVal3 n.natAbs

theorem natVal3_zero : natVal3 0 = 0 := by
  rw [natVal3]
  simp

theorem natVal3_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : natVal3 n = 0 := by
  rw [natVal3]
  simp [h]

theorem natVal3_succ {n : ℕ} (h0 : 0 < n) (hd : 3 ∣ n) :
    natVal3 n = natVal3 (n / 3) + 1 := by
  rw [natVal3]
  simp [h0, hd]

theorem three_dvd_natAbs (n : ℤ) : (3 : ℤ) ∣ n ↔ 3 ∣ n.natAbs :=
  Int.ofNat_dvd_left

theorem intVal3_eq_zero_of_not_dvd {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) :
    intVal3 n = 0 := by
  have : ¬ 3 ∣ n.natAbs := fun hd => h ((three_dvd_natAbs n).mpr hd)
  simpa [intVal3] using natVal3_of_not_dvd this

theorem natAbs_ediv_three {n : ℤ} (hd : (3 : ℤ) ∣ n) :
    (n / 3).natAbs = n.natAbs / 3 := by
  obtain ⟨k, hk⟩ := hd
  have hdiv : n / 3 = k := by
    rw [hk, Int.mul_ediv_cancel_left k (by decide : (3 : ℤ) ≠ 0)]
  have h3 : (3 : ℤ).natAbs = 3 := rfl
  rw [hdiv, hk, Int.natAbs_mul, h3, Nat.mul_div_right k.natAbs (by decide : 0 < 3)]

theorem intVal3_succ_of_dvd {n : ℤ} (hne : n ≠ 0) (hd : (3 : ℤ) ∣ n) :
    intVal3 n = intVal3 (n / 3) + 1 := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hne
  have hdn : 3 ∣ n.natAbs := (three_dvd_natAbs n).mp hd
  have hdiv := natAbs_ediv_three hd
  simpa [intVal3, hdiv] using natVal3_succ hpos hdn

theorem natVal3_mul_not_dvd {a b : ℕ} (ha : ¬ 3 ∣ a) :
    natVal3 (a * b) = natVal3 b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb0 : b = 0
    · subst hb0
      simp [natVal3_zero]
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      by_cases hbd : 3 ∣ b
      · have hprod : 3 ∣ a * b := dvd_mul_of_dvd_right hbd a
        have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h0 => by
          subst h0
          exact ha (by decide))
        have hpos : 0 < a * b := Nat.mul_pos ha0 hbpos
        have hlt : b / 3 < b := Nat.div_lt_self hbpos (by decide : 1 < 3)
        rw [natVal3_succ hpos hprod, Nat.mul_div_assoc a hbd, ih (b / 3) hlt,
          natVal3_succ hbpos hbd]
      · have hprod : ¬ 3 ∣ a * b := by
          intro h
          have hmod : (a * b) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
          have ha1 : a % 3 = 1 ∨ a % 3 = 2 := by
            have hlt : a % 3 < 3 := Nat.mod_lt a (by decide)
            have hne : a % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.mpr ha
            omega
          have hb1 : b % 3 = 1 ∨ b % 3 = 2 := by
            have hlt : b % 3 < 3 := Nat.mod_lt b (by decide)
            have hne : b % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.mpr hbd
            omega
          have hmul : (a * b) % 3 = (a % 3 * (b % 3)) % 3 := Nat.mul_mod a b 3
          rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;>
            simp [hmul, ha1, hb1] at hmod
        rw [natVal3_of_not_dvd hprod, natVal3_of_not_dvd hbd]

theorem intVal3_mul_not_dvd {a b : ℤ} (ha : ¬ (3 : ℤ) ∣ a) :
    intVal3 (a * b) = intVal3 b := by
  have han : ¬ 3 ∣ a.natAbs := fun hd => ha ((three_dvd_natAbs a).mpr hd)
  simpa [intVal3, Int.natAbs_mul] using
    natVal3_mul_not_dvd (a := a.natAbs) (b := b.natAbs) han

/-- Distinct residuals are Mealy-inequivalent.  For `gain` not divisible by `3` and
`s != t`, the constant word of length `v3 (s - t) + 1` already separates the signed
traces from `s` and from `t`. -/
theorem residual_separation {gain s t u : ℤ}
    (hgain : ¬ (3 : ℤ) ∣ gain) (hne : s ≠ t) :
    signedTrace gain s (List.replicate (intVal3 (s - t) + 1) u) ≠
      signedTrace gain t (List.replicate (intVal3 (s - t) + 1) u) := by
  generalize hval : intVal3 (s - t) = n
  induction n using Nat.strongRecOn generalizing s t with
  | ind n ih =>
    have hst : s - t ≠ 0 := sub_ne_zero.mpr hne
    rw [List.replicate_succ, signedTrace_cons, signedTrace_cons]
    by_cases hc : s ≡ t [ZMOD 3]
    · have hdvd : (3 : ℤ) ∣ s - t := (cong_iff_dvd_sub s t).mp hc
      have hout : signedOut s u = signedOut t u :=
        (signedOut_eq_iff_cong s t u).mpr hc
      simp [hout]
      set s' := signedNext gain s u
      set t' := signedNext gain t u
      have hdiff' : s' = t' + gain * ((s - t) / 3) :=
        signedNext_diff_of_cong hc gain u
      have hq : (s - t) / 3 ≠ 0 := by
        intro hq0
        have hmul : 3 * ((s - t) / 3) = s - t := Int.mul_ediv_cancel' hdvd
        exact hst (by simpa [hq0] using hmul.symm)
      have hgain0 : gain ≠ 0 := fun hg => hgain (by simp [hg])
      have hne' : s' ≠ t' := by
        intro heq
        have : gain * ((s - t) / 3) = 0 := by linarith
        exact (mul_ne_zero hgain0 hq) this
      have hsucc : intVal3 (s - t) = intVal3 ((s - t) / 3) + 1 :=
        intVal3_succ_of_dvd hst hdvd
      have hnpos : 1 ≤ n := by omega
      have hval' : intVal3 (s' - t') = n - 1 := by
        have hst' : s' - t' = gain * ((s - t) / 3) := by linarith
        have : intVal3 (s' - t') = intVal3 ((s - t) / 3) := by
          simpa [hst'] using intVal3_mul_not_dvd (a := gain) (b := (s - t) / 3) hgain
        omega
      have hlt : n - 1 < n := Nat.sub_lt (Nat.succ_le.mp hnpos) (by decide : 0 < 1)
      have hsep := ih (n - 1) hlt hne' hval'
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      simpa [hn'] using hsep
    · have hn0 : n = 0 := by
        have : intVal3 (s - t) = 0 :=
          intVal3_eq_zero_of_not_dvd (fun hd => hc ((cong_iff_dvd_sub s t).mpr hd))
        exact hval ▸ this
      subst hn0
      simp [signedOut_ne_of_not_cong hc]

theorem lambda3_trace_translate (s k : ℤ) :
    ∀ w, signedTrace 3 (s + 3 * k) w = signedTrace 3 s w := by
  intro w
  induction w generalizing s with
  | nil => rfl
  | cons u rest ih =>
    have hout : signedOut (s + 3 * k) u = signedOut s u := by
      have harg : s + 3 * k + u = s + u + 3 * k := by ring
      simpa [signedOut, harg] using lsdZ_add_mul3 (s + u) k
    have hnext : signedNext 3 (s + 3 * k) u = signedNext 3 s u + 3 * k := by
      have hc : (s + 3 * k) ≡ s [ZMOD 3] := by
        refine (cong_iff_dvd_sub (s + 3 * k) s).mpr ?_
        simp
      have hdiff := signedNext_diff_of_cong hc 3 u
      have hdiv : (s + 3 * k - s) / 3 = k := by
        have : s + 3 * k - s = 3 * k := by ring
        rw [this, Int.mul_ediv_cancel_left k (by decide : (3 : ℤ) ≠ 0)]
      simpa [hdiv] using hdiff
    rw [signedTrace_cons, signedTrace_cons, hout, hnext, ih]

theorem lambda3_translate_equiv (s k u : ℤ) (n : ℕ) :
    signedTrace 3 (s + 3 * k) (List.replicate n u) =
      signedTrace 3 s (List.replicate n u) :=
  lambda3_trace_translate s k _

end Problems.BalancedTernary
