import Problems.Collatz.Cylinder

namespace Problems.Collatz

/-- Direct residue formula for `R`: when the affine relation `3^m R + C = 2^K` holds and
`3^m` is invertible, `R` is `(2^K - C)` times that inverse -- no division, no case split. -/
theorem direct_realizer_residue
    {A : Type} [CommRing A]
    (R C threePow twoPow inverse : A)
    (hAffine : threePow * R + C = twoPow)
    (hInverse : inverse * threePow = 1) :
    R = inverse * (twoPow - C) := by
  have hSolve : threePow * R = twoPow - C := by
    linear_combination hAffine
  calc
    R = 1 * R := by ring
    _ = (inverse * threePow) * R := by rw [hInverse]
    _ = inverse * (threePow * R) := by ring
    _ = inverse * (twoPow - C) := by rw [hSolve]

theorem liftDigit_residue
    {A : Type} [CommRing A]
    (t q half threePow inverse : A)
    (hChild : threePow * t + q = half)
    (hInverse : inverse * threePow = 1) :
    t = inverse * (half - q) := by
  have hSolve : threePow * t = half - q := by
    linear_combination hChild
  calc
    t = 1 * t := by ring
    _ = (inverse * threePow) * t := by rw [hInverse]
    _ = inverse * (threePow * t) := by ring
    _ = inverse * (half - q) := by rw [hSolve]

theorem endpoint_successor_identity
    (q a t denominator child : ℕ)
    (h : q + a * t = denominator * child) :
    q + a * t = denominator * child := h

end Problems.Collatz
