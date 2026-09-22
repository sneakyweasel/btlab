import BTCalculus.Algebra
import Problems.BalancedTernary.SignedDigitResidual

namespace Problems.BalancedTernary

open BTCalculus

/-!
Product-control residual ``λ · DZ(s + d₁ d₂)``. The step is the existing
signed-digit map evaluated at the raw product. This file does not
repeat ``D_mul`` / ``lsdZ_mul``.
-/

def productRaw (d1 d2 : ℤ) : ℤ :=
  d1 * d2

def productNext (gain s d1 d2 : ℤ) : ℤ :=
  signedNext gain s (d1 * d2)

def productOut (s d1 d2 : ℤ) : ℤ :=
  signedOut s (d1 * d2)

/-- Control pairs factor through the raw contribution. -/
theorem product_factor_through_raw (gain s d1 d2 : ℤ) :
    productNext gain s d1 d2 = signedNext gain s (productRaw d1 d2) :=
  rfl

theorem trit_mul_is_trit {a b : ℤ} (ha : isTrit a) (hb : isTrit b) :
    isTrit (a * b) := by
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [ha, hb, isTrit]

theorem product_raw_is_trit {d1 d2 : ℤ} (h1 : isTrit d1) (h2 : isTrit d2) :
    isTrit (productRaw d1 d2) :=
  trit_mul_is_trit h1 h2

theorem product_origin {gain d1 d2 : ℤ}
    (h1 : isTrit d1) (h2 : isTrit d2) :
    productNext gain 0 d1 d2 = 0 := by
  have hu := isTrit_natAbs (trit_mul_is_trit h1 h2)
  simpa [productNext] using origin_trit_forcing (gain := gain) (u := d1 * d2) hu

/-- Origin-reachable residual of two-trit product forcing is ``{0}``. -/
theorem product_residual_closure {gain d1 d2 : ℤ}
    (h1 : isTrit d1) (h2 : isTrit d2) :
    productNext gain 0 d1 d2 = 0 :=
  product_origin h1 h2

theorem product_raw_quotient :
    productRaw 1 1 = 1 ∧
      productRaw (-1) (-1) = 1 ∧
      productRaw 1 (-1) = -1 ∧
      productRaw (-1) 1 = -1 ∧
      productRaw 0 0 = 0 ∧
      productRaw 0 1 = 0 ∧
      productRaw 1 0 = 0 ∧
      productRaw 0 (-1) = 0 ∧
      productRaw (-1) 0 = 0 := by
  native_decide

def product3Raw (d1 d2 d3 : ℤ) : ℤ :=
  d1 * d2 * d3

def product3Next (gain s d1 d2 d3 : ℤ) : ℤ :=
  signedNext gain s (d1 * d2 * d3)

theorem product3_factor_through_raw (gain s d1 d2 d3 : ℤ) :
    product3Next gain s d1 d2 d3 = signedNext gain s (product3Raw d1 d2 d3) :=
  rfl

theorem trit_mul3_is_trit {a b c : ℤ}
    (ha : isTrit a) (hb : isTrit b) (hc : isTrit c) :
    isTrit (a * b * c) :=
  trit_mul_is_trit (trit_mul_is_trit ha hb) hc

theorem product3_origin {gain d1 d2 d3 : ℤ}
    (h1 : isTrit d1) (h2 : isTrit d2) (h3 : isTrit d3) :
    product3Next gain 0 d1 d2 d3 = 0 := by
  have hu := isTrit_natAbs (trit_mul3_is_trit h1 h2 h3)
  simpa [product3Next] using origin_trit_forcing (gain := gain) (u := d1 * d2 * d3) hu

/-- Doubled-trit coefficient on a product: ``u = 2 d₁ d₂``. -/
def doubledProductNext (gain s d1 d2 : ℤ) : ℤ :=
  signedNext gain s (2 * d1 * d2)

theorem doubled_product_factor (gain s d1 d2 : ℤ) :
    doubledProductNext gain s d1 d2 = signedNext gain s (2 * productRaw d1 d2) := by
  simp [doubledProductNext, productRaw]
  ring_nf

theorem doubled_product_all_plus (gain s : ℤ) :
    doubledProductNext gain s 1 1 = signedNext gain s 2 := by
  simp [doubledProductNext]

end Problems.BalancedTernary
