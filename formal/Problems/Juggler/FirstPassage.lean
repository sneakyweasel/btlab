import Problems.Juggler.Drift
import Problems.Juggler.Envelope

namespace Problems.Juggler

/-!
# First-passage times

Ordinary stopping time versus coefficient / drift stopping time.
Neither is assumed finite. The already-known arrow is

```
HasFiniteCoeffStop n  →  HasFiniteStop n
```

The statement `∀ n ≥ 2, HasFiniteCoeffStop n` is not proved here.
-/

def HasFiniteStop (n : ℕ) : Prop :=
  ∃ k > 0, floorPower^[k] n < n

def HasFiniteCoeffStop (n : ℕ) : Prop :=
  ∃ k > 0, trajectoryExponentGap n k

/-- Isolated research target. Not a theorem. -/
def FiniteCoeffStopConjecture : Prop :=
  ∀ n, 2 ≤ n → HasFiniteCoeffStop n

theorem hasFiniteStop_of_contracts {n k : ℕ}
    (hk : 0 < k) (hlt : floorPower^[k] n < n) :
    HasFiniteStop n :=
  ⟨k, hk, hlt⟩

theorem hasFiniteCoeffStop_of_gap {n k : ℕ}
    (hk : 0 < k) (hgap : trajectoryExponentGap n k) :
    HasFiniteCoeffStop n :=
  ⟨k, hk, hgap⟩

/-- A realized word that lands strictly below `n` is a first-passage stop. -/
theorem hasFiniteStop_of_imageLt {n : ℕ} {w : List Branch}
    (_hw : follows n w) (hlt : image n w < n) : HasFiniteStop n := by
  have hlen : 0 < w.length := by
    cases w with
    | nil =>
      change n < n at hlt
      exact (lt_irrefl n hlt).elim
    | cons _ _ => simp
  refine ⟨w.length, hlen, ?_⟩
  simpa [image_eq_iterate] using hlt

/-- The `k = 1` case of `power_bound_lt_pow` is a first-passage stop. -/
theorem hasFiniteStop_of_power_bound_lt_pow {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < 2 ^ w.length) : HasFiniteStop n :=
  hasFiniteStop_of_imageLt hw (by
    simpa using power_bound_lt_pow (k := 1) hn hw (by simpa using hgap))

/-- Already known: a positive combinatorial drift on the actual
itinerary forces a strict descent. Wraps `power_bound_contracts`. -/
theorem coeffStop_implies_stop {n : ℕ} (hn : 2 ≤ n)
    (h : HasFiniteCoeffStop n) : HasFiniteStop n := by
  obtain ⟨k, hk, hgap⟩ := h
  have hw : follows n (word n k) := follows_word_self n k
  have hlt : floorPower^[k] n < n := by
    have hgap' : 3 ^ oddCount (word n k) < 2 ^ (word n k).length := by
      simpa [word_length] using trajectoryExponentGap_iff.mp hgap
    have := power_bound_contracts hn hw hgap'
    simpa [word_length] using this
  exact ⟨k, hk, hlt⟩

end Problems.Juggler
