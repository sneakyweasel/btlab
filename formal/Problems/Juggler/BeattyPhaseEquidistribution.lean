import Problems.Juggler.BeattyRotation
import Problems.Juggler.BeattyCertificateCluster

/-!
# Equidistribution of the certificate phases

The exact logarithmic phases specialize the uniform empirical law of every
irrational real rotation. The reusable proof lives in `BeattyRotation`.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology

/-- The exact certificate phases have the uniform empirical limiting law. -/
theorem certificatePhase_equidistributed :
    Tendsto (empiricalLaw certificatePhase) atTop (𝓝 unitPhaseLaw) := by
  have he : certificatePhase = fun n : ℕ => Int.fract ((n : ℝ)*(1/PaperBThreshold.beta)) := by
    funext n
    simp only [certificatePhase_eq_fract, div_eq_mul_inv, one_mul]
  rw [he]
  exact irrational_rotation_equidistributed certificateSlope_irrational

end Problems.Juggler.BeattyPhase
