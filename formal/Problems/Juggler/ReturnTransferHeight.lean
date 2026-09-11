import Problems.Juggler.ReturnGapHeight
import Problems.Juggler.ReturnWordBounds
import Problems.Juggler.ReturnCycleTransfers

namespace Problems.Juggler.ReturnTransferHeight

open ReturnGapHeight ReturnWordLoss ReturnWordBounds

/-- Positive odd pairs supply positive even natural gaps and exact real casts. -/
theorem odd_pair_gap {l u : ℕ} (hlt : l < u) (ho : l%2=1 ∧ u%2=1) :
    0 < u-l ∧ (u-l)%2=0 ∧ ((u-l : ℕ) : ℝ)=(u : ℝ)-l := by
  refine ⟨by omega,by omega,?_⟩
  exact Nat.cast_sub hlt.le

/-- Two prescribed C transfers of ordered odd pairs give the DC gap bounds. -/
theorem dc_gap_from_pairs {m : ℕ} {l u : ℕ → ℕ}
    (hm : 2^24 ≤ m) (hmin : ∀ i < 2, m ≤ l i)
    (hlt : ∀ i < 3, l i < u i) (hodd : ∀ i < 3, l i%2=1 ∧ u i%2=1)
    (hstep : ∀ i < 2, eval wordC (l i)= l (i+1) ∧ eval wordC (u i)= u (i+1)) :
    6 ≤ u 0-l 0 ∧ (26240/59049 : ℝ)*(m : ℝ)^(13/128 : ℝ) < (u 0-l 0 : ℕ) := by
  have h0 := odd_pair_gap (hlt 0 (by omega)) (hodd 0 (by omega))
  have h1 := odd_pair_gap (hlt 1 (by omega)) (hodd 1 (by omega))
  have h2 := odd_pair_gap (hlt 2 (by omega)) (hodd 2 (by omega))
  have hmR : (2 : ℝ)^24 ≤ m := by exact_mod_cast hm
  have hs0 := c_pair_from_floor hmR (by exact_mod_cast hmin 0 (by omega)) (hlt 0 (by omega)).le
  have hs1 := c_pair_from_floor hmR (by exact_mod_cast hmin 1 (by omega)) (hlt 1 (by omega)).le
  rw [(hstep 0 (by omega)).1,(hstep 0 (by omega)).2] at hs0
  rw [(hstep 1 (by omega)).1,(hstep 1 (by omega)).2] at hs1
  rw [← h0.2.2,← h1.2.2] at hs0
  rw [← h1.2.2,← h2.2.2] at hs1
  exact dc_two_transfer_bounds (by omega) h0.1 h1.1 h2.1 h0.2.1 h1.2.1 h2.2.1
    (c_slope_lt hmR).le hs0 hs1

/-- The additional W transfer yields the exact LR gap bounds. -/
theorem lr_gap_from_pairs {m : ℕ} {l u : ℕ → ℕ}
    (hm : 2^128 ≤ m) (hmin : ∀ i < 3, m ≤ l i)
    (hlt : ∀ i < 4, l i < u i) (hodd : ∀ i < 4, l i%2=1 ∧ u i%2=1)
    (hstep : ∀ i < 2, eval wordC (l i)= l (i+1) ∧ eval wordC (u i)= u (i+1))
    (hW : eval wordW (l 2)=l 3 ∧ eval wordW (u 2)=u 3) :
    8 ≤ u 0-l 0 ∧ (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) < (u 0-l 0 : ℕ) := by
  have h0 := odd_pair_gap (hlt 0 (by omega)) (hodd 0 (by omega))
  have h1 := odd_pair_gap (hlt 1 (by omega)) (hodd 1 (by omega))
  have h2 := odd_pair_gap (hlt 2 (by omega)) (hodd 2 (by omega))
  have h3 := odd_pair_gap (hlt 3 (by omega)) (hodd 3 (by omega))
  have hmR : (2 : ℝ)^128 ≤ m := by exact_mod_cast hm
  have hm24 : (2 : ℝ)^24 ≤ m := by linarith
  have hs0 := c_pair_from_floor hm24 (by exact_mod_cast hmin 0 (by omega)) (hlt 0 (by omega)).le
  have hs1 := c_pair_from_floor hm24 (by exact_mod_cast hmin 1 (by omega)) (hlt 1 (by omega)).le
  have hs2 := w_pair_from_floor hmR (by exact_mod_cast hmin 2 (by omega)) (hlt 2 (by omega)).le
  rw [(hstep 0 (by omega)).1,(hstep 0 (by omega)).2] at hs0
  rw [(hstep 1 (by omega)).1,(hstep 1 (by omega)).2] at hs1
  rw [hW.1,hW.2] at hs2
  rw [← h0.2.2,← h1.2.2] at hs0
  rw [← h1.2.2,← h2.2.2] at hs1
  rw [← h2.2.2,← h3.2.2] at hs2
  exact lr_three_transfer_bounds (by omega) h0.1 h1.1 h2.1 h3.1
    h0.2.1 h1.2.1 h2.2.1 h3.2.1 (c_slope_large_lt hmR).le (w_slope_lt hmR).le hs0 hs1 hs2

/-- A cycle placement certificate now suffices for the full DC height conclusion. -/
theorem periodic_extrema_dc_from_pairs {C : Set ℕ} {m M : ℕ} {l u : ℕ → ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M<m^3)
    (hl0 : l 0=ReturnCells.oe M.sqrt) (hu0 : u 0=ReturnCells.ooe m)
    (hmin : ∀ i < 2, m ≤ l i)
    (hlt : ∀ i < 3, l i < u i) (hodd : ∀ i < 3, l i%2=1 ∧ u i%2=1)
    (hstep : ∀ i < 2, eval wordC (l i)= l (i+1) ∧ eval wordC (u i)= u (i+1)) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128 := by
  have hg := dc_gap_from_pairs hm hmin hlt hodd hstep
  rw [hl0,hu0] at hg
  exact periodic_extrema_dc_height D hm hM hg.1 hg.2

/-- The genuine third pair certificate gives the sharp and clean LR strips. -/
theorem periodic_extrema_lr_from_pairs {C : Set ℕ} {m M : ℕ} {l u : ℕ → ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3)
    (hl0 : l 0=ReturnCells.oe M.sqrt) (hu0 : u 0=ReturnCells.ooe m)
    (hmin : ∀ i < 3, m ≤ l i)
    (hlt : ∀ i < 4, l i < u i) (hodd : ∀ i < 4, l i%2=1 ∧ u i%2=1)
    (hstep : ∀ i < 2, eval wordC (l i)= l (i+1) ∧ eval wordC (u i)= u (i+1))
    (hW : eval wordW (l 2)=l 3 ∧ eval wordW (u 2)=u 3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64 := by
  have hg := lr_gap_from_pairs hm hmin hlt hodd hstep hW
  rw [hl0,hu0] at hg
  exact periodic_extrema_lr_height D (by omega) hM hg.1 hg.2


/-- A typed DC transfer chain supplies the original scalar interface. -/
theorem dc_gap_from_chain {m : ℕ} (hm : 2 ^ 24 ≤ m)
    (T : ReturnSeams.TransferChain m 2 ReturnSeams.dcWords) :
    6 ≤ T.upperNat 0 - T.lowerNat 0 ∧
    (26240/59049 : ℝ) * (m : ℝ) ^ (13/128 : ℝ) <
      (T.upperNat 0 - T.lowerNat 0 : ℕ) := by
  exact dc_gap_from_pairs hm (fun _ hi => T.minimum_nat hi)
    (fun _ hi => T.ordered_nat hi) (fun _ hi => T.odd_nat hi)
    (fun _ hi => T.next_nat hi)

/-- A typed C,C,W transfer chain supplies the later scalar interface. -/
theorem lr_gap_from_chain {m : ℕ} (hm : 2 ^ 128 ≤ m)
    (T : ReturnSeams.TransferChain m 3 ReturnSeams.lrWords) :
    8 ≤ T.upperNat 0 - T.lowerNat 0 ∧
    (2/5 : ℝ) * (m : ℝ) ^ (13/128+1-(3:ℝ)^41/2^65) <
      (T.upperNat 0 - T.lowerNat 0 : ℕ) := by
  apply lr_gap_from_pairs hm (fun _ hi => T.minimum_nat hi)
    (fun _ hi => T.ordered_nat hi) (fun _ hi => T.odd_nat hi)
  · intro i hi
    simpa [ReturnSeams.lrWords, hi] using T.next_nat (show i < 3 by omega)
  · simpa [ReturnSeams.lrWords] using T.next_nat (show 2 < 3 by omega)

/-- Every actual cubic cycle on the DC domain supplies the two gap bounds. -/
theorem dc_cycle_gap {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M<m^3) :
    6 ≤ ReturnCells.ooe m-ReturnCells.oe M.sqrt ∧
    (26240/59049 : ℝ)*(m : ℝ)^(13/128 : ℝ) <
      (ReturnCells.ooe m-ReturnCells.oe M.sqrt : ℕ) := by
  obtain ⟨T, hl0, hu0⟩ := ReturnSeams.periodicExtrema_dc_chain D hm hM
  have hg := dc_gap_from_chain hm T
  simpa only [hl0,hu0] using hg

/-- Every actual cubic cycle on the LR domain supplies the third gap bound. -/
theorem lr_cycle_gap {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3) :
    8 ≤ ReturnCells.ooe m-ReturnCells.oe M.sqrt ∧
    (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) <
      (ReturnCells.ooe m-ReturnCells.oe M.sqrt : ℕ) := by
  obtain ⟨T, hl0, hu0⟩ := ReturnSeams.periodicExtrema_lr_chain D hm hM
  have hg := lr_gap_from_chain hm T
  simpa only [hl0,hu0] using hg

/-- The unconditional actual-cycle DC height strip, including its integer form. -/
theorem dc_cycle_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128 := by
  have hg := dc_cycle_gap D hm hM
  exact periodic_extrema_dc_height D hm hM hg.1 hg.2

/-- The unconditional actual-cycle LR strip with exact and clean exponents. -/
theorem lr_cycle_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^128 ≤ m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64 := by
  have hg := lr_cycle_gap D hm hM
  exact periodic_extrema_lr_height D (by omega) hM hg.1 hg.2

/-- Ordinary finite-period orbit hypotheses suffice for the DC theorem. -/
theorem periodicOrbit_dc_height {m M k : ℕ} (hk : 0<k)
    (hp : floorPower^[k] m=m)
    (hbound : ∀ j<k,m≤floorPower^[j] m ∧ floorPower^[j] m≤M)
    (hmax : ∃ j<k,floorPower^[j] m=M) (hm : 2^24≤m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128 := by
  exact dc_cycle_height (CubicReturn.periodicExtrema_of_orbit hk hp hbound hmax) hm hM

/-- Ordinary finite-period orbit hypotheses suffice for both LR exponents. -/
theorem periodicOrbit_lr_height {m M k : ℕ} (hk : 0<k)
    (hp : floorPower^[k] m=m)
    (hbound : ∀ j<k,m≤floorPower^[j] m ∧ floorPower^[j] m≤M)
    (hmax : ∃ j<k,floorPower^[j] m=M) (hm : 2^128≤m) (hM : M<m^3) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64 := by
  exact lr_cycle_height (CubicReturn.periodicExtrema_of_orbit hk hp hbound hmax) hm hM

end Problems.Juggler.ReturnTransferHeight
