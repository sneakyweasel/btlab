import Problems.Juggler.Dynamics

/-!
# Factor complexity of the odd-branch parity sequence: the finite part

`oddCubeParity k = Nat.sqrt ((2k+1)^3) % 2` is the parity of the odd-step image of the odd
start `2k+1`, that is the second letter of its itinerary.  Every binary word of length at
most six occurs among its first values, and the sixty-four words of length six are first
exhausted at exactly 574 terms.  These are closed computations, checked by the kernel.

The asymptotic statements (a quadratic lower bound on the factor count and the resulting
non-automaticity) rest on Boshernitzan's equidistribution theorem and are recorded as a
human proof in the ledger; nothing of that kind is claimed in this file.
-/

namespace Problems.Juggler

/-- Parity of `⌊(2k+1)^{3/2}⌋`: the letter following the odd step from `2k+1`. -/
def oddCubeParity (k : ℕ) : ℕ := Nat.sqrt ((2 * k + 1) ^ 3) % 2

/-- The parity sequence is the odd-branch image parity of the laboratory map. -/
theorem oddCubeParity_eq_floorPower (k : ℕ) :
    oddCubeParity k = floorPower (2 * k + 1) % 2 := by
  have hodd : (2 * k + 1) % 2 = 1 := by omega
  rw [floorPower_odd_eq hodd]
  rfl

/-- The first `n` letters. -/
def parityPrefix (n : ℕ) : List ℕ := (List.range n).map oddCubeParity

/-- All windows of length `L` of a finite word, in order of position. -/
def windows (s : List ℕ) (L : ℕ) : List (List ℕ) :=
  (List.range (s.length + 1 - L)).map (fun i => (s.drop i).take L)

/-- Number of distinct windows of length `L`. -/
def factorCount (s : List ℕ) (L : ℕ) : ℕ := ((windows s L).dedup).length

theorem parityPrefix_eight : parityPrefix 8 = [1, 1, 1, 0, 1, 0, 0, 0] := by
  decide +kernel

/-- Every word of length three occurs within the first 18 letters. -/
theorem factorCount_three_saturates : factorCount (parityPrefix 18) 3 = 8 := by
  decide +kernel

/-- Every word of length four occurs within the first 48 letters. -/
theorem factorCount_four_saturates : factorCount (parityPrefix 48) 4 = 16 := by
  decide +kernel

/-- Every word of length five occurs within the first 169 letters. -/
theorem factorCount_five_saturates : factorCount (parityPrefix 169) 5 = 32 := by
  decide +kernel

/-- Every word of length six occurs within the first 574 letters ... -/
theorem factorCount_six_saturates : factorCount (parityPrefix 574) 6 = 64 := by
  decide +kernel

/-- ... and one of them is still missing after 573: the exhaustion index is exactly 574. -/
theorem factorCount_six_not_before : factorCount (parityPrefix 573) 6 = 63 := by
  decide +kernel

end Problems.Juggler
