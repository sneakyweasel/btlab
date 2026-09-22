import Problems.Juggler.Preimages

/-!
# Exact transport of odd predecessor weights

The formal odd branch is used at every step, with all original parity
conditions retained. Finite fibre reindexing is exact at every depth.
The analytic application at depth two uses Paper B's written estimate.
-/

namespace Problems.Juggler.OddPredecessorTransport

open Finset

def oddMap (n : ℕ) : ℕ := (n ^ 3).sqrt

theorem oddMap_eq_step {n : ℕ} (hn : n % 2 = 1) : oddMap n = floorPower n :=
  (floorPower_odd_eq hn).symm

theorem oddMap_cell (n : ℕ) :
    (oddMap n) ^ 2 ≤ n ^ 3 ∧ n ^ 3 < (oddMap n + 1) ^ 2 :=
  floor_sqrt_eq_iff_sq_interval.mp rfl

theorem oddMap_injective : Function.Injective oddMap := by
  intro a b h
  apply odd_preimage_unique (oddMap_cell a)
  simpa [h] using oddMap_cell b

theorem oddMap_monotone : Monotone oddMap := by
  intro a b hab
  exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hab 3)

theorem oddMap_strictMono : StrictMono oddMap :=
  oddMap_monotone.strictMono_of_injective oddMap_injective

theorem le_oddMap (n : ℕ) : n ≤ oddMap n := by
  apply Nat.le_sqrt.mpr
  cases n with
  | zero => simp
  | succ n => nlinarith [Nat.zero_le n, Nat.zero_le (n ^ 2)]

theorem le_iterate (d n : ℕ) : n ≤ oddMap^[d] n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_oddMap _)

/-- Includes the parity of the endpoint: depth two means three odd states. -/
def oddChain : ℕ → ℕ → Prop
  | 0, n => n % 2 = 1
  | d + 1, n => n % 2 = 1 ∧ oddChain d (oddMap n)

instance (d n : ℕ) : Decidable (oddChain d n) := by
  induction d generalizing n with
  | zero => exact inferInstanceAs (Decidable (n % 2 = 1))
  | succ d ih => exact @instDecidableAnd _ _ inferInstance (ih _)

theorem chain_actual {d n : ℕ} (hc : oddChain d n) :
    floorPower^[d] n = oddMap^[d] n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← oddMap_eq_step hc.1]
    exact ih hc.2

theorem chain_iff_follows (d n : ℕ) :
    oddChain d n ↔ follows n (List.replicate (d + 1) Branch.odd) := by
  induction d generalizing n with
  | zero => simp [oddChain, follows]
  | succ d ih =>
    change (n % 2 = 1 ∧ oddChain d (oddMap n)) ↔
      (n % 2 = 1 ∧ follows (floorPower n) (List.replicate (d + 1) Branch.odd))
    apply and_congr_right
    intro hn
    rw [← oddMap_eq_step hn]
    exact ih _

theorem chain_endpoint {d n : ℕ} (hc : oddChain d n) :
    oddMap^[d] n % 2 = 1 := by
  induction d generalizing n with
  | zero => exact hc
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    exact ih hc.2

def ancestors (d m : ℕ) : Finset ℕ :=
  (range (m + 1)).filter (fun n => oddChain d n ∧ oddMap^[d] n = m)

def weight (d m : ℕ) : ℕ := (ancestors d m).card

theorem mem_ancestors {d m n : ℕ} :
    n ∈ ancestors d m ↔ oddChain d n ∧ oddMap^[d] n = m := by
  simp only [ancestors, mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have := le_iterate d n
    exact ⟨by omega, h⟩

theorem weight_le_one (d m : ℕ) : weight d m ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact (oddMap_injective.iterate d)
    ((mem_ancestors.mp ha).2.trans (mem_ancestors.mp hb).2.symm)

theorem weight_even_zero (d m : ℕ) (hm : m % 2 = 0) : weight d m = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hc, he⟩ := mem_ancestors.mp hn
  have hp := chain_endpoint hc
  rw [he, hm] at hp
  contradiction

def sources (d B : ℕ) (I : Finset ℕ) : Finset ℕ :=
  (range (B + 1)).filter (fun n => oddChain d n ∧ oddMap^[d] n ∈ I)

theorem source_fibre {d B m : ℕ} {I : Finset ℕ}
    (hm : m ∈ I) (hB : ∀ y ∈ I, y ≤ B) :
    (sources d B I).filter (fun n => oddMap^[d] n = m) = ancestors d m := by
  ext n
  simp only [sources, mem_filter, mem_range, mem_ancestors]
  constructor
  · exact fun h => ⟨h.1.2.1, h.2⟩
  · intro h
    have hn := le_iterate d n
    have hmB := hB m hm
    exact ⟨⟨by omega, h.1, h.2 ▸ hm⟩, h.2⟩

theorem weighted_reindex (d B : ℕ) (I : Finset ℕ) (hB : ∀ m ∈ I, m ≤ B)
    (g : ℕ → ℂ) :
    ∑ m ∈ I, (weight d m : ℂ) * g m =
      ∑ n ∈ sources d B I, g (oddMap^[d] n) := by
  have hmaps : ∀ n ∈ sources d B I, oddMap^[d] n ∈ I := by
    intro n hn
    exact (mem_filter.mp hn).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro m hm
  rw [source_fibre hm hB]
  have he : ∑ n ∈ ancestors d m, g (oddMap^[d] n) =
      ∑ _n ∈ ancestors d m, g m := by
    apply sum_congr rfl
    intro n hn
    rw [(mem_ancestors.mp hn).2]
  rw [he]
  simp [weight, nsmul_eq_mul]

theorem two_chain (n : ℕ) : oddChain 2 n ↔
    n % 2 = 1 ∧ oddMap n % 2 = 1 ∧ oddMap (oddMap n) % 2 = 1 := Iff.rfl

theorem two_step_scale {n : ℕ} (hn : 0 < n) :
    (oddMap (oddMap n)) ^ 4 ≤ n ^ 9 ∧
      n ^ 9 < 64 * (oddMap (oddMap n) + 1) ^ 4 := by
  let a := oddMap n
  let m := oddMap a
  have h1 := oddMap_cell n
  have h2 := oddMap_cell a
  have ha : 1 ≤ a := (show 1 ≤ n from hn).trans (le_oddMap n)
  change m ^ 4 ≤ n ^ 9 ∧ n ^ 9 < 64 * (m + 1) ^ 4
  constructor
  · have h21 := Nat.pow_le_pow_left h2.1 2
    have h11 := Nat.pow_le_pow_left h1.1 3
    dsimp [a, m] at *
    nlinarith only [h21, h11]
  · have hc : n ^ 3 < 4 * a ^ 2 := by
      have : (a + 1) ^ 2 ≤ 4 * a ^ 2 := by nlinarith
      exact h1.2.trans_le this
    calc
      n ^ 9 = (n ^ 3) ^ 3 := by ring
      _ < (4 * a ^ 2) ^ 3 := Nat.pow_lt_pow_left hc (by decide)
      _ = 64 * (a ^ 3) ^ 2 := by ring
      _ < 64 * ((m + 1) ^ 2) ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left h2.2 (by decide)) (by decide)
      _ = 64 * (m + 1) ^ 4 := by ring

theorem source_interval {a b n x y : ℕ}
    (hx : n ≤ x) (hy : x ≤ y)
    (hn : a < oddMap^[2] n) (hyy : oddMap^[2] y ≤ b) :
    a < oddMap^[2] x ∧ oddMap^[2] x ≤ b := by
  have hm := oddMap_monotone.iterate 2
  exact ⟨hn.trans_le (hm hx), (hm hy).trans hyy⟩

theorem exponent_budget :
    (4 / 9 : ℚ) * (127 / 128) = 127 / 288 ∧
    (4 / 9 : ℚ) - 127 / 288 = 1 / 288 ∧
    (24 : ℚ) / 60 < 127 / 288 ∧
    (1 / 60 : ℚ) < (4 / 9) / 24 := by norm_num

theorem one_cell_budget :
    (2 / 3 : ℚ) * (127 / 128) = 127 / 192 ∧
    (24 : ℚ) / 40 < 127 / 192 ∧
    (127 / 192 : ℚ) < 2 / 3 - 1 / 50000 := by norm_num

end Problems.Juggler.OddPredecessorTransport
