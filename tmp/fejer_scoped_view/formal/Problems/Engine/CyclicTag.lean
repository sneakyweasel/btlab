import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Exact identities for the rewrite that drops the first bit and appends
`[false]` or `[true, true]`. Empty has no successor. These statements are
KNOWN. They are not a universality theorem.
-/

def tagStep : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (rest ++ [false])
  | true :: rest => some (rest ++ [true, true])

theorem tagStep_nil : tagStep [] = none := rfl

theorem tagStep_zero_fixed : tagStep [false] = some [false] := rfl

/-- Packet seed `101` maps to `0111`. -/
theorem tagStep_seed_one_zero_one :
    tagStep [true, false, true] = some [false, true, true, true] := rfl

theorem tagStep_length_ge {w w' : List Bool} (h : tagStep w = some w') :
    w.length ≤ w'.length := by
  cases w with
  | nil =>
    simp [tagStep] at h
  | cons b rest =>
    cases b with
    | false =>
      simp [tagStep] at h
      subst h
      simp
    | true =>
      simp [tagStep] at h
      subst h
      simp [List.length_cons, List.length_append]

end Problems.Engine
