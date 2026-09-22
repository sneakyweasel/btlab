import BTCalculus.MismatchedCubicQuotient
import BTCalculus.MismatchedCubicInvariant
import BTCalculus.XCubeStateComplexity

noncomputable section

namespace BTCalculus

open Polynomial

/-!
Unified Newton-stratum packaging of the cubic residual fibre laws.

At horizon ``k`` and deficit ``r`` with ``r+1 ≤ k``, depth ``m = k-1-r``.
-/

theorem newtonStratum_n2 {k r : Nat} (hr : r + 1 ≤ k) (p q : Int) :
    (3 : Int) ^ k ∣ n2Resid (k - 1 - r) p - n2Resid (k - 1 - r) q ↔
      (3 : Int) ^ r ∣ p - q :=
  depthDeficit_n2_visibility hr p q

theorem newtonStratum_n1 {k r : Nat} (hk : 1 ≤ k) (hr : r + 1 ≤ k)
    {p q d : Int} (hd : p - q = (3 : Int) ^ r * d) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q ↔
      (3 : Int) ^ (k - 1 - r) ∣ d * (p + q + (3 : Int) ^ (k - 1 - r)) :=
  n1_after_n2_iff hk hr hd

theorem newtonStratum_n1_val {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hnp : ¬ (3 : Int) ^ r ∣ p)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    p = q :=
  n1_val_lt_injective hr hk hpw hqw hnp hN2 hN1

theorem newtonStratum_n21_fibre {k r : Nat} (hr : 1 ≤ r) (hk : r + 1 ≤ k)
    {p q : Int}
    (hpw : balWidth (k - 1 - r) p) (hqw : balWidth (k - 1 - r) q)
    (hne : p ≠ q)
    (hN2 : (3 : Int) ^ r ∣ p - q)
    (hN1 : (3 : Int) ^ k ∣ n1Resid (k - 1 - r) p - n1Resid (k - 1 - r) q) :
    (3 : Int) ^ r ∣ p :=
  n21_fibre_in_pow hr hk hpw hqw hne hN2 hN1

theorem newtonStratum_n0_le {m r : Nat} (hm : m ≤ 3 * r) (u : Int) :
    n0Resid m ((3 : Int) ^ r * u) = (3 : Int) ^ (3 * r - m) * u ^ 3 :=
  n0_scaled_of_le hm u

theorem newtonStratum_n0_ge {m r : Nat} (hm : 3 * r ≤ m) (u : Int) :
    n0Resid m ((3 : Int) ^ r * u) = n0Resid (m - 3 * r) u :=
  n0_scaled_of_ge hm u

theorem newtonStratum_q {k r : Nat}
    (hr : r + 1 ≤ k) (hk : 4 * r + 1 ≤ k) (u : Int) :
    n0Resid (k - 1 - r) ((3 : Int) ^ r * u) = qCubic (k - 1 - 4 * r) u :=
  q_from_exhausted hr hk u

theorem newtonStratum_q_one_family {t K : Nat}
    (ht : 1 ≤ t) (hK : 1 ≤ K) (b c : Int) :
    (3 : Int) ^ K ∣ qCubic t (1 + (3 : Int) ^ t * b) -
        qCubic t (1 + (3 : Int) ^ t * c) ↔
      (3 : Int) ^ (K - 1) ∣ b - c :=
  q_one_family_dvd ht hK b c

theorem newtonStratum_core_width {m r : Nat} (hr : r ≤ m) (u : Int) :
    balWidth m ((3 : Int) ^ r * u) ↔ balWidth (m - r) u :=
  balWidth_pow_iff hr u

theorem newtonStratum_n1_core {k r : Nat} (hr : r + 1 ≤ k)
    (h2 : 2 * r + 2 ≤ k) (u : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
      (3 : Int) ^ (2 * r + 1) * u ^ 2 :=
  n1_on_core_mod hr h2 u

theorem newtonStratum_q_unit_family {t K : Nat} (ht : 1 ≤ t) (hK : 1 ≤ K)
    {a : Int} (ha : ¬ (3 : Int) ∣ a) (b c : Int) :
    (3 : Int) ^ K ∣ qCubic t (a + (3 : Int) ^ t * b) -
        qCubic t (a + (3 : Int) ^ t * c) ↔
      (3 : Int) ^ (K - 1) ∣ b - c :=
  q_unit_family_dvd ht hK ha b c

theorem newtonStratum_zero_spine_n1 {k m : Nat} (h : k ≤ 2 * m) :
    (3 : Int) ^ k ∣ n1Resid m 0 :=
  zero_spine_n1 h

theorem newtonStratum_n1_square {k r : Nat} (h2 : 2 * r + 2 ≤ k) (u v : Int) :
    (3 : Int) ^ k ∣ n1Resid (k - 1 - r) ((3 : Int) ^ r * u) -
        n1Resid (k - 1 - r) ((3 : Int) ^ r * v) ↔
      (3 : Int) ^ (k - 2 * r - 1) ∣ u ^ 2 - v ^ 2 :=
  n1_core_square_iff h2 u v

theorem newtonStratum_unit_square {W : Nat} {u v : Int}
    (hu : balWidth W u) (hv : balWidth W v)
    (hnu : ¬ (3 : Int) ∣ u) (hnv : ¬ (3 : Int) ∣ v)
    (h : (3 : Int) ^ W ∣ u ^ 2 - v ^ 2) :
    u = v ∨ u = -v :=
  unit_square_pm hu hv hnu hnv h

theorem newtonStratum_n0_neg {k m : Nat} {u : Int} :
    (3 : Int) ^ k ∣ n0Resid m u - n0Resid m (-u) ↔
      (3 : Int) ^ k ∣ n0Resid m u :=
  n0_eq_of_neg

end BTCalculus
