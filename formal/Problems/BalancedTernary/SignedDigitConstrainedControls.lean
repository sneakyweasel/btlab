import Problems.BalancedTernary.SignedDigitResidualMinimality

namespace Problems.BalancedTernary

open BTCalculus

/-!
Any word of length ``v_3(s-t)+1`` separates coprime-gain residuals.
A constant/cyclic letter is not required. This file does not repeat
the finite/infinite phase law.
-/

/-- For `gain` not divisible by `3` and `s != t`, *every* word of length `v3 (s - t) + 1`
separates the signed traces. A common cyclic letter is not required, so a control-language
restriction cannot rescue a pair that this length already tells apart. -/
theorem any_word_separation {gain s t : ℤ} {w : List ℤ}
    (hgain : ¬ (3 : ℤ) ∣ gain) (hne : s ≠ t)
    (hw : w.length = intVal3 (s - t) + 1) :
    signedTrace gain s w ≠ signedTrace gain t w := by
  generalize hval : intVal3 (s - t) = n
  induction n using Nat.strongRecOn generalizing s t w with
  | ind n ih =>
    have hst : s - t ≠ 0 := sub_ne_zero.mpr hne
    match w with
    | [] =>
      simp at hw
    | u :: rest =>
      have hlen : rest.length = n := by
        have : rest.length + 1 = intVal3 (s - t) + 1 := by
          simpa [List.length_cons] using hw
        omega
      rw [signedTrace_cons, signedTrace_cons]
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
        have hrest : rest.length = intVal3 (s' - t') + 1 := by
          have : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
          omega
        exact ih (n - 1) hlt hne' hrest hval'
      · have hn0 : n = 0 := by
          have : intVal3 (s - t) = 0 :=
            intVal3_eq_zero_of_not_dvd (fun hd => hc ((cong_iff_dvd_sub s t).mpr hd))
          exact hval ▸ this
        subst hn0
        simp [signedOut_ne_of_not_cong hc]

/-- Existence of any legal word of the critical length is enough. -/
theorem common_word_separation {gain s t : ℤ} {w : List ℤ}
    (hgain : ¬ (3 : ℤ) ∣ gain) (hne : s ≠ t)
    (hw : w.length = intVal3 (s - t) + 1) :
    signedTrace gain s w ≠ signedTrace gain t w :=
  any_word_separation hgain hne hw

/-- Constrained controls cannot destroy the unrestricted ``λ=3`` translation. -/
theorem lambda3_constrained_symmetry (s k : ℤ) (w : List ℤ) :
    signedTrace 3 (s + 3 * k) w = signedTrace 3 s w :=
  lambda3_trace_translate s k w

end Problems.BalancedTernary
