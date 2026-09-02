import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

/-!
# Trajectory drift

`G` along an actual itinerary is the combinatorial drift of `itinerary n k`.
This file does not mention stopping times or certificates.
-/

def trajectoryDrift (n k : ℕ) : ℤ :=
  driftG (itinerary n k)

def trajectoryExponentGap (n k : ℕ) : Prop :=
  exponentGap (itinerary n k)

theorem trajectoryExponentGap_iff {n k : ℕ} :
    trajectoryExponentGap n k ↔ 3 ^ oddCount (itinerary n k) < 2 ^ k := by
  simp [trajectoryExponentGap, exponentGap, itinerary_length]

theorem follows_itinerary_self (n k : ℕ) : follows n (itinerary n k) :=
  (follows_iff_itinerary n (itinerary n k)).mpr (by simp [itinerary_length])

end Problems.Juggler
