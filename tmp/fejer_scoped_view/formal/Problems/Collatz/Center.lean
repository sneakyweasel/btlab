import Problems.Collatz.Endpoint

namespace Problems.Collatz

/-- The unreduced numerator of `R - C / (twoPow - threePow)` is exactly
`twoPow * (R - X)` whenever the affine endpoint equation holds. -/
theorem affineCenter_start_numerator
    (twoPow threePow R C X : ℤ)
    (hEndpoint : threePow * R + C = twoPow * X) :
    (twoPow - threePow) * R - C = twoPow * (R - X) := by
  linear_combination -hEndpoint

/-- The unreduced numerator of `X - C / (twoPow - threePow)` is exactly
`threePow * (R - X)`. -/
theorem affineCenter_endpoint_numerator
    (twoPow threePow R C X : ℤ)
    (hEndpoint : threePow * R + C = twoPow * X) :
    (twoPow - threePow) * X - C = threePow * (R - X) := by
  linear_combination -hEndpoint

/-- Cross-multiplied centered scaling, avoiding every division and sign
case:

`twoPow * (X - n*) = threePow * (R - n*)`.
-/
theorem affineCenter_scaling_cross
    (twoPow threePow R C X : ℤ)
    (hEndpoint : threePow * R + C = twoPow * X) :
    twoPow * ((twoPow - threePow) * X - C) =
      threePow * ((twoPow - threePow) * R - C) := by
  rw [affineCenter_endpoint_numerator _ _ _ _ _ hEndpoint]
  rw [affineCenter_start_numerator _ _ _ _ _ hEndpoint]
  ring

/-- If the endpoint is represented by its least-positive residue plus a
nonnegative `3^m` lift, then `M ≤ X`. -/
theorem endpointRepresentative_le
    (M threePow q X : ℕ)
    (hX : X = M + q * threePow) :
    M ≤ X := by
  omega

end Problems.Collatz
