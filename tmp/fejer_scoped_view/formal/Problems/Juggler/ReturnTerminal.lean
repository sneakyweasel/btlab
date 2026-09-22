import Problems.Juggler.ReturnWordLoss
import Problems.Juggler.ReturnRankedCycle

namespace Problems.Juggler.ReturnTerminal

/-- Consecutive members of the original periodic set, with their orientation. -/
structure AdjacentIn (C : Set ℕ) (x y : ℕ) : Prop where
  left_mem : x ∈ C
  right_mem : y ∈ C
  ordered : x < y
  no_between : ¬ ∃ z ∈ C, x < z ∧ z < y

theorem same_parity_mono {x y : ℕ} (hxy : x ≤ y) (hp : x % 2 = y % 2) :
    floorPower x ≤ floorPower y := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx
  · exact floorPower_even_mono hx (by omega) hxy
  · exact floorPower_odd_mono hx (by omega) hxy

theorem even_image_lt_odd_image {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hx : x ∈ C) (hy : y ∈ C) (hxe : x % 2 = 0) (hyo : y % 2 = 1) :
    floorPower x < floorPower y := by
  have he := D.even_image_lt_min_image hm hM hx hxe
  have ho := floorPower_odd_mono (D.min_odd hm hM) hyo (D.bounds _ hy).1
  rw [floorPower_even_eq hxe]
  rw [floorPower_odd_eq (D.min_odd hm hM)] at ho
  exact he.trans_le ho

/-- A common actual branch preserves global adjacency in a cubic periodic set. -/
theorem AdjacentIn.step {C : Set ℕ} {m M x y : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (h : AdjacentIn C x y) (hp : x % 2 = y % 2) :
    AdjacentIn C (floorPower x) (floorPower y) := by
  have hmono := same_parity_mono h.ordered.le hp
  have hlt : floorPower x < floorPower y := lt_of_le_of_ne hmono
    (fun he => (ne_of_lt h.ordered) (D.inj h.left_mem h.right_mem he))
  refine ⟨D.closed _ h.left_mem, D.closed _ h.right_mem, hlt, ?_⟩
  rintro ⟨z, hz, hxz, hzy⟩
  obtain ⟨v, hv, hvz⟩ := D.preimage hz
  have hpar : v % 2 = x % 2 := by
    by_contra hn
    rcases Nat.mod_two_eq_zero_or_one x with hxe | hxo
    · have hvo : v % 2 = 1 := by omega
      have hh := even_image_lt_odd_image D hm hM h.right_mem hv (by omega) hvo
      omega
    · have hve : v % 2 = 0 := by omega
      have hh := even_image_lt_odd_image D hm hM hv h.left_mem hve hxo
      omega
  have hxv : x < v := by
    by_contra hn
    have hh := same_parity_mono (show v ≤ x by omega) hpar
    omega
  have hvy : v < y := by
    by_contra hn
    have hh := same_parity_mono (show y ≤ v by omega) (hp.symm.trans hpar.symm)
    omega
  exact h.no_between ⟨v, hv, hxv, hvy⟩

/-- Every actual common prefix preserves the original adjacency. -/
theorem AdjacentIn.image {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    {x y : ℕ} {P : List Branch} (h : AdjacentIn C x y)
    (hx : follows x P) (hy : follows y P) :
    AdjacentIn C (image x P) (image y P) := by
  induction P generalizing x y with
  | nil => exact h
  | cons b P ih =>
    cases b with
    | even => exact ih (h.step D hm hM (hx.1.trans hy.1.symm)) hx.2 hy.2
    | odd => exact ih (h.step D hm hM (hx.1.trans hy.1.symm)) hx.2 hy.2

/-- A globally adjacent odd/even pair is the absolute cut and maps to the extrema. -/
theorem AdjacentIn.cut_extrema {C : Set ℕ} {m M h s : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hadj : AdjacentIn C h s) (hho : h % 2 = 1) (hse : s % 2 = 0) :
    h < m ^ 2 ∧ m ^ 2 < s ∧
      (∀ x ∈ C, x % 2 = 1 → x ≤ h) ∧
      (∀ x ∈ C, x % 2 = 0 → s ≤ x) ∧
      floorPower h = M ∧ floorPower s = m := by
  have hhcut : h < m ^ 2 := (D.parity hM hadj.left_mem).mp hho
  have hscut : m ^ 2 < s := by
    have hn : ¬ s < m ^ 2 := by
      intro hs
      have := (D.parity hM hadj.right_mem).mpr hs
      omega
    have hmpar := D.min_odd hm hM
    have hmp : m ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hmpar]
    omega
  have hmaxodd : ∀ x ∈ C, x % 2 = 1 → x ≤ h := by
    intro x hx hxo
    have hxcut := (D.parity hM hx).mp hxo
    by_contra hn
    exact hadj.no_between ⟨x, hx, by omega, by omega⟩
  have hmineven : ∀ x ∈ C, x % 2 = 0 → s ≤ x := by
    intro x hx hxe
    have hxcut : m ^ 2 ≤ x := by
      have hn : ¬ x < m ^ 2 := by
        intro hxlt
        have := (D.parity hM hx).mpr hxlt
        omega
      omega
    by_contra hn
    exact hadj.no_between ⟨x, hx, by omega, by omega⟩
  refine ⟨hhcut, hscut, hmaxodd, hmineven, ?_, ?_⟩
  · obtain ⟨v, hv, hvM⟩ := D.preimage D.max_mem
    have hvo : v % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one v with hve | hvo
      · have hh := floorPower_even_lt (show 2 ≤ v by have := (D.bounds _ hv).1; omega) hve
        have hb := (D.bounds _ hv).2
        omega
      · exact hvo
    have hle := floorPower_odd_mono hvo hho (hmaxodd v hv hvo)
    have hbound := (D.bounds _ (D.closed _ hadj.left_mem)).2
    omega
  · obtain ⟨v, hv, hvm⟩ := D.preimage D.min_mem
    have hve : v % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one v with hve | hvo
      · exact hve
      · have hh := floorPower_odd_gt (show 3 ≤ v by have := (D.bounds _ hv).1; omega) hvo
        have hb := (D.bounds _ hv).1
        omega
    have hle := floorPower_even_mono hse hve (hmineven v hv hve)
    have hbound := (D.bounds _ (D.closed _ hadj.right_mem)).1
    omega

theorem quarter_power_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (3 / 4 : ℝ)) ^ 4 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The mixed passage contracts the integer gap across the absolute cut. -/
theorem mixed_gap_of_cells {m h s q t : ℕ}
    (hh1 : 1 ≤ h) (hh : h < m^2) (hs : m^2 < s)
    (hq : q^2 ≤ m^3) (ht : h^3 < (t+1)^4) :
    (q : ℤ) - t < (s : ℤ) - h := by
  let X : ℝ := (m : ℝ)^2
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hh0 : (0 : ℝ) < h := by linarith
  have hhX : (h : ℝ) < X := by dsimp [X]; exact_mod_cast hh
  have hXs : X+1 ≤ (s : ℝ) := by
    dsimp [X]
    exact_mod_cast Nat.succ_le_of_lt hs
  have hq2 : (q : ℝ)^2 ≤ (m : ℝ)^3 := by exact_mod_cast hq
  have hq4 : (q : ℝ)^4 ≤ X^3 := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (q : ℝ)^2) hq2 2
    dsimp [X]
    nlinarith only [hp]
  have hqR : (q : ℝ) ≤ X^(3/4 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (Real.rpow_nonneg (by positivity) _)
    rw [quarter_power_cube X (by positivity)]
    exact hq4
  have ht4 : (h : ℝ)^3 < ((t : ℝ)+1)^4 := by exact_mod_cast ht
  have htR : (h : ℝ)^(3/4 : ℝ) < (t : ℝ)+1 := by
    apply lt_of_pow_lt_pow_left₀ 4 (by positivity)
    rw [quarter_power_cube (h : ℝ) (Nat.cast_nonneg h)]
    exact ht4
  have hconc := ReturnWordLoss.rpow_sub_le hh0 hhX.le
    (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) ≤ 1)
  have hpow : (h : ℝ)^((3/4 : ℝ)-1) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
      hh1r (by norm_num : (3/4 : ℝ)-1 ≤ 0)
  have hmul := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hhX.le)
  have hreal : (q : ℝ) - t < (s : ℝ) - h := by nlinarith
  exact_mod_cast hreal

theorem mixed_gap {m h s : ℕ}
    (hh1 : 1 ≤ h) (hh : h < m^2) (hs : m^2 < s) :
    ((m^3).sqrt : ℤ) - ReturnCells.oe h < (s : ℤ) - h :=
  mixed_gap_of_cells hh1 hh hs (Nat.sqrt_le' _) (ReturnCells.oe_cell h).2

/-- The complete terminal geometry, with every path interpreted on the original
actual periodic set. This record contains no contraction premise for the prefix. -/
structure TerminalCut (C : Set ℕ) (m M : ℕ) where
  next : ℕ
  lowerWord : List Branch
  upperWord : List Branch
  commonPrefix : List Branch
  suffix : List Branch
  highOdd : ℕ
  lowEven : ℕ
  source_adjacent : AdjacentIn C m next
  induced : ReturnWordFactorization.InducedPair lowerWord upperWord
  factorization : ReturnWordFactorization.Factorization lowerWord upperWord commonPrefix suffix
  lower_guard : follows m lowerWord
  upper_guard : follows next upperWord
  lower_return : image m lowerWord = next
  upper_return : image next upperWord = m
  prefix_lower_guard : follows m commonPrefix
  prefix_upper_guard : follows next commonPrefix
  prefix_lower : image m commonPrefix = highOdd
  prefix_upper : image next commonPrefix = lowEven
  cut_adjacent : AdjacentIn C highOdd lowEven
  high_odd : highOdd % 2 = 1
  low_even : lowEven % 2 = 0
  high_below_cut : highOdd < m ^ 2
  low_above_cut : m ^ 2 < lowEven
  largest_odd : ∀ x ∈ C, x % 2 = 1 → x ≤ highOdd
  smallest_even : ∀ x ∈ C, x % 2 = 0 → lowEven ≤ x
  high_image : floorPower highOdd = M
  low_image : floorPower lowEven = m
  suffix_lower_guard : follows M.sqrt suffix
  suffix_upper_guard : follows (CubicReturn.O m) suffix
  suffix_lower : image M.sqrt suffix = m
  suffix_upper : image (CubicReturn.O m) suffix = next
  mixed_gap_positive : 0 < ((CubicReturn.O m : ℕ) : ℤ) - M.sqrt
  mixed_gap_contracts : ((CubicReturn.O m : ℕ) : ℤ) - M.sqrt <
    (lowEven : ℤ) - highOdd

private theorem min_ge_five {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    5 ≤ m := by
  by_contra hn
  have hodd := D.min_odd hm hM
  have hm3 : m = 3 := by omega
  subst m
  have hs : floorPower^[6] 3 = 1 := by decide +kernel
  have hb := (D.bounds _ (D.iter_mem D.min_mem 6)).1
  rw [hs] at hb
  omega

/-- A primitive guarded section produces the complete cut while retaining all
three expanded word totals. -/
theorem terminal_cut_from_section {C : Set ℕ} {m M a b : ℕ} {y : ℕ → ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (ha : 0 < a) (hb : 0 < b) (h0 : y 0 = m)
    (hr : ReturnSeams.RankedReturn a b y [.odd, .odd, .even] [.odd, .even])
    (hsection : ReturnSeams.PrefixSection C (a + b) y) (hcop : Nat.Coprime a b) :
    ∃ T : TerminalCut C m M,
      T.lowerWord.length + T.upperWord.length = 3 * a + 2 * b ∧
      oddCount T.lowerWord + oddCount T.upperWord = 2 * a + b ∧
      evenCount T.lowerWord + evenCount T.upperWord = a + b := by
  obtain ⟨U, V, hw, ht, hlength, hodd, heven⟩ :=
    hr.primitive_terminal ha hb hcop ReturnWordFactorization.InducedPair.initial
  have hU : follows m U ∧ image m U = y 1 := by
    simpa [h0] using ht.lower 0 (by decide)
  have hV : follows (y 1) V ∧ image (y 1) V = m := by
    simpa [h0] using ht.upper 1 (by decide) (by decide)
  obtain ⟨P, Q, hF, hmP, hvP, hho, _, hse, _, hQl, hQr, hQli, hQri⟩ :=
    ReturnWordFactorization.induced_terminal_actual_factorization hw hU.1 hV.1 hU.2 hV.2
  have hadj : AdjacentIn C m (y 1) := {
    left_mem := D.min_mem
    right_mem := hsection.member 1 (by omega)
    ordered := by simpa [h0] using ht.ordered 0 1 (by decide) (by decide)
    no_between := by simpa [h0] using hsection.adjacent (i := 0) (by omega) }
  have hcut := hadj.image D (by omega) hM hmP hvP
  obtain ⟨hhcut, hscut, hmaxodd, hmineven, hhM, hsm⟩ :=
    hcut.cut_extrema D (by omega) hM hho hse
  have hleft : floorPower (floorPower (image m P)) = M.sqrt := by
    rw [hhM, floorPower_even_eq (D.max_even (by omega))]
  have hright : floorPower (floorPower (image (y 1) P)) = CubicReturn.O m := by
    rw [hsm, floorPower_odd_eq (D.min_odd (by omega) hM)]
    rfl
  rw [hleft] at hQl hQli
  rw [hright] at hQr hQri
  have hoe : ReturnCells.oe (image m P) = M.sqrt := by
    have hhroot : ((image m P) ^ 3).sqrt = M := by
      simpa [floorPower_odd_eq hho] using hhM
    change (((image m P) ^ 3).sqrt).sqrt = M.sqrt
    rw [hhroot]
  have hgap := mixed_gap (show 1 ≤ image m P by
    have := (D.bounds _ hcut.left_mem).1; omega) hhcut hscut
  rw [hoe] at hgap
  have hpositive := D.even_image_lt_min_image (by omega) hM D.max_mem (D.max_even (by omega))
  let T : TerminalCut C m M := {
    next := y 1
    lowerWord := U
    upperWord := V
    commonPrefix := P
    suffix := Q
    highOdd := image m P
    lowEven := image (y 1) P
    source_adjacent := hadj
    induced := hw
    factorization := hF
    lower_guard := hU.1
    upper_guard := hV.1
    lower_return := hU.2
    upper_return := hV.2
    prefix_lower_guard := hmP
    prefix_upper_guard := hvP
    prefix_lower := rfl
    prefix_upper := rfl
    cut_adjacent := hcut
    high_odd := hho
    low_even := hse
    high_below_cut := hhcut
    low_above_cut := hscut
    largest_odd := hmaxodd
    smallest_even := hmineven
    high_image := hhM
    low_image := hsm
    suffix_lower_guard := hQl
    suffix_upper_guard := hQr
    suffix_lower := hQli
    suffix_upper := hQri
    mixed_gap_positive := by omega
    mixed_gap_contracts := hgap }
  norm_num [oddCount, evenCount] at hlength hodd heven
  refine ⟨T, ?_, ?_, ?_⟩
  · change U.length + V.length = 3 * a + 2 * b
    omega
  · change oddCount U + oddCount V = 2 * a + b
    omega
  · change evenCount U + evenCount V = a + b
    omega

/-- Connected actual cubic periodic sets supply the entire primitive terminal
construction and its global odd/even cut identification. -/
theorem periodicExtrema_terminal_cut {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 3 ≤ m) (hM : M < m ^ 3)
    (hconnected : ∀ x ∈ C, ∀ z ∈ C, ∃ k, floorPower^[k] x = z) :
    Nonempty (TerminalCut C m M) := by
  have hm5 := min_ge_five D hm hM
  obtain ⟨a, b, y, ha, hb, h0, _, hr, _, hsection, hcop⟩ :=
    ReturnSeams.periodicExtrema_return_section D hm5 hM
  obtain ⟨T, _, _, _⟩ := terminal_cut_from_section D hm hM ha hb h0 hr hsection
    (hcop hconnected)
  exact ⟨T⟩

/-- A terminal cut tied to the same complete sorted orbit witness. Its word
totals count distinct primitive states, not the supplied period. -/
structure TerminalOrbitCut {m M k : ℕ} (S : ReturnSeams.PeriodicOrbitModel m M k)
    extends TerminalCut (Set.range (fun j : ℕ => floorPower^[j] m)) m M where
  length_total : lowerWord.length + upperWord.length = S.length
  odd_total : oddCount lowerWord + oddCount upperWord =
    (Finset.univ.filter (fun i => S.state i % 2 = 1)).card
  even_total : evenCount lowerWord + evenCount upperWord =
    (Finset.univ.filter (fun i => S.state i % 2 = 0)).card
  least_period : S.length = Function.minimalPeriod floorPower m

end Problems.Juggler.ReturnTerminal

namespace Problems.Juggler.ReturnSeams.PeriodicOrbitModel

/-- The fixed sorted orbit witness supplies terminal geometry and primitive totals. -/
theorem terminal_cut {m M k : ℕ} (S : PeriodicOrbitModel m M k)
    (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (ReturnTerminal.TerminalOrbitCut S) := by
  have D := S.periodicExtrema
  have hm5 := ReturnTerminal.min_ge_five D hm hM
  obtain ⟨a, b, y, ha, hb, h0, _, hr, _, hsection, hlength, hodd, heven, hcop⟩ :=
    return_section_of_sorted D hm5 hM S.length_pos S.state S.next S.ordered
      S.member (fun _ hx => S.complete hx) S.step S.min_eq S.max_eq
  obtain ⟨T, hTlength, hTodd, hTeven⟩ :=
    ReturnTerminal.terminal_cut_from_section D hm hM ha hb h0 hr hsection
      (hcop S.connected)
  exact ⟨{
    toTerminalCut := T
    length_total := hTlength.trans hlength
    odd_total := hTodd.trans hodd
    even_total := hTeven.trans heven
    least_period := S.least_period hM }⟩

end Problems.Juggler.ReturnSeams.PeriodicOrbitModel

namespace Problems.Juggler.ReturnTerminal

/-- Ordinary period data constructs a shared model and its primitive terminal cut. -/
theorem periodicOrbit_terminal_totals {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    ∃ S : ReturnSeams.PeriodicOrbitModel m M k, Nonempty (TerminalOrbitCut S) := by
  obtain ⟨S⟩ := ReturnSeams.periodicOrbit_model hk hp hbound hmax
  exact ⟨S, S.terminal_cut hm hM⟩

/-- An ordinary positive actual period suffices; the given period need not be
least, since the complete orbit set is reduced to its primitive permutation. -/
theorem periodicOrbit_terminal_cut {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (TerminalCut (Set.range (fun j : ℕ => floorPower^[j] m)) m M) := by
  obtain ⟨S, ⟨T⟩⟩ := periodicOrbit_terminal_totals hk hp hbound hmax hm hM
  exact ⟨T.toTerminalCut⟩

/-- Closed minimum itineraries retain primitive totals even when the word repeats. -/
theorem cycleMin_terminal_totals {m M : ℕ} {w : List Branch} (h : CycleMin m w)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    ∃ S : ReturnSeams.PeriodicOrbitModel m M w.length, Nonempty (TerminalOrbitCut S) := by
  exact periodicOrbit_terminal_totals (show 0 < w.length from h.1.2.2)
    (cycle_iterate_period h.1) (fun j hj => ⟨h.2 j hj, hupper j hj⟩) hmax hm hM

/-- The cycle-minimum interface also supplies the complete terminal certificate. -/
theorem cycleMin_terminal_cut {m M : ℕ} {w : List Branch} (h : CycleMin m w)
    (hupper : ∀ j < w.length, floorPower^[j] m ≤ M)
    (hmax : ∃ j < w.length, floorPower^[j] m = M) (hm : 3 ≤ m) (hM : M < m ^ 3) :
    Nonempty (TerminalCut (Set.range (fun j : ℕ => floorPower^[j] m)) m M) := by
  apply periodicOrbit_terminal_cut (show 0 < w.length from h.1.2.2)
    (cycle_iterate_period h.1) (fun j hj => ⟨h.2 j hj, hupper j hj⟩) hmax hm hM

end Problems.Juggler.ReturnTerminal
