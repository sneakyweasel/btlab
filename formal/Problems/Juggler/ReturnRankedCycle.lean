import Problems.Juggler.ReturnSeams
import Problems.Juggler.CubicRotation
import Problems.Juggler.CubicConsequences

namespace Problems.Juggler.ReturnSeams


/-- One complete sorted witness for an ordinary periodic orbit. The supplied
period may repeat the primitive orbit; `length` counts its distinct states. -/
structure PeriodicOrbitModel (m M k : ℕ) where
  length : ℕ
  length_pos : 0 < length
  state : Fin length → ℕ
  next : Equiv.Perm (Fin length)
  ordered : StrictMono state
  mem : ∀ i, ∃ j < k, state i = floorPower^[j] m
  covers : ∀ j, ∃ i, state i = floorPower^[j] m
  step : ∀ i, state (next i) = floorPower (state i)
  cycleOn : next.IsCycleOn Set.univ
  min_eq : state ⟨0, length_pos⟩ = m
  max_eq : state ⟨length - 1, by omega⟩ = M
  period_pos : 0 < k
  periodic : floorPower^[k] m = m

namespace PeriodicOrbitModel

variable {m M k : ℕ} (S : PeriodicOrbitModel m M k)
include S

theorem member (i : Fin S.length) :
    S.state i ∈ Set.range (fun j : ℕ => floorPower^[j] m) := by
  obtain ⟨j, _, hj⟩ := S.mem i
  exact ⟨j, hj.symm⟩

theorem complete {x : ℕ} (hx : x ∈ Set.range (fun j : ℕ => floorPower^[j] m)) :
    ∃ i, S.state i = x := by
  obtain ⟨j, rfl⟩ := hx
  exact S.covers j

theorem periodicExtrema :
    CubicReturn.PeriodicExtrema (Set.range (fun j : ℕ => floorPower^[j] m)) m M := by
  refine ⟨⟨0, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [← S.max_eq]
    exact S.member _
  · intro x hx
    obtain ⟨i, rfl⟩ := S.complete hx
    constructor
    · have hi := S.ordered.monotone (show (⟨0, S.length_pos⟩ : Fin S.length) ≤ i from
        Nat.zero_le _)
      simpa only [S.min_eq] using hi
    · have hi := S.ordered.monotone (show i ≤ (⟨S.length - 1, by have := S.length_pos; omega⟩ :
        Fin S.length) from show i.val ≤ S.length - 1 by omega)
      simpa only [S.max_eq] using hi
  · rintro x ⟨j, rfl⟩
    exact ⟨j + 1, Function.iterate_succ_apply' floorPower j m⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := S.complete hx
    obtain ⟨n, hn, hp⟩ := S.next.injective.mem_periodicPts i
    refine ⟨n, hn, ?_⟩
    change S.next^[n] i = i at hp
    change floorPower^[n] (S.state i) = S.state i
    rw [← cubic_conjugacy_iterate S.state S.next floorPower S.step, hp]

theorem connected : ∀ x ∈ Set.range (fun j : ℕ => floorPower^[j] m),
    ∀ z ∈ Set.range (fun j : ℕ => floorPower^[j] m),
    ∃ n, floorPower^[n] x = z := by
  intro x hx z hz
  obtain ⟨i, rfl⟩ := S.complete hx
  obtain ⟨j, rfl⟩ := S.complete hz
  have hc : S.next.IsCycleOn (↑(Finset.univ : Finset (Fin S.length))) := by
    simpa using S.cycleOn
  obtain ⟨n, _, hn⟩ := hc.exists_pow_eq (by simp : i ∈ (Finset.univ : Finset (Fin S.length)))
    (by simp : j ∈ (Finset.univ : Finset (Fin S.length)))
  refine ⟨n, ?_⟩
  rw [← cubic_conjugacy_iterate S.state S.next floorPower S.step]
  simpa only [← Equiv.Perm.coe_pow] using congrArg S.state hn

theorem least_period (hM : M < m ^ 3) :
    S.length = Function.minimalPeriod floorPower m := by
  have D := S.periodicExtrema
  have hp := cubicBand_cycle_minimalPeriod S.length_pos S.state S.ordered S.next
    (fun i => D.band hM (S.member i)) S.step
    (fun i j => S.connected _ (S.member i) _ (S.member j)) ⟨0, S.length_pos⟩
  simpa only [S.min_eq] using hp.symm

end PeriodicOrbitModel

/-- Any two members of one finite periodic orbit are connected by forward steps. -/
theorem periodic_orbit_reachable {α : Type*} {f : α → α} {x : α} {k i j : ℕ}
    (hp : f^[k] x = x) (hi : i < k) :
    ∃ n, f^[n] (f^[i] x) = f^[j] x := by
  refine ⟨j + (k - i), ?_⟩
  rw [← Function.iterate_add_apply]
  have he : j + (k - i) + i = j + k := by omega
  rw [he, Function.iterate_add_apply, hp]

/-- A bounded periodic set has a sorted complete finite permutation model. -/
theorem periodicExtrema_sorted_model {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ) (p : Equiv.Perm (Fin L)),
      StrictMono c ∧ (∀ i, c i ∈ C) ∧ (∀ x ∈ C, ∃ i, c i = x) ∧
      (∀ i, c (p i) = floorPower (c i)) ∧
      c ⟨0, hL⟩ = m ∧ c ⟨L - 1, by omega⟩ = M := by
  classical
  let s := (Finset.Icc m M).filter (fun x => x ∈ C)
  have hs : ∀ x, x ∈ s ↔ x ∈ C := by
    intro x
    simp only [s, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨D.bounds x h, h⟩⟩
  have hL : 0 < s.card := Finset.card_pos.mpr ⟨m, (hs m).mpr D.min_mem⟩
  let c : Fin s.card → ℕ := s.orderEmbOfFin rfl
  have hc : StrictMono c := (s.orderEmbOfFin rfl).strictMono
  have hcC : ∀ i, c i ∈ C := fun i =>
    (hs (c i)).mp (s.orderEmbOfFin_mem rfl i)
  have hcover : ∀ x ∈ C, ∃ i, c i = x := by
    intro x hx
    have hr : x ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [s.range_orderEmbOfFin rfl]
      exact (hs x).mpr hx
    exact hr
  have hclosed : ∀ x ∈ s, floorPower x ∈ s := fun x hx =>
    (hs _).mpr (D.closed x ((hs x).mp hx))
  have hinj : Set.InjOn floorPower s := by
    intro x hx y hy he
    exact D.inj ((hs x).mp hx) ((hs y).mp hy) he
  obtain ⟨p, hstep⟩ := sorted_invariant_permutation s floorPower hclosed hinj
  change ∀ i, c (p i) = floorPower (c i) at hstep
  refine ⟨s.card, hL, c, p, hc, hcC, hcover, hstep, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hcover m D.min_mem
    have hle := hc.monotone (show (⟨0, hL⟩ : Fin s.card) ≤ i from Nat.zero_le _)
    have hge := (D.bounds _ (hcC ⟨0, hL⟩)).1
    omega
  · obtain ⟨i, hi⟩ := hcover M D.max_mem
    have hle := hc.monotone (show i ≤ (⟨s.card - 1, by omega⟩ : Fin s.card) from
      show i.val ≤ s.card - 1 by omega)
    have hge := (D.bounds _ (hcC ⟨s.card - 1, by omega⟩)).2
    omega

/-- Sorting a single actual periodic orbit also supplies full transitivity. -/
theorem periodicOrbit_sorted_model {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    ∃ (L : ℕ) (hL : 0 < L) (c : Fin L → ℕ) (p : Equiv.Perm (Fin L)),
      StrictMono c ∧ (∀ i, ∃ j < k, c i = floorPower^[j] m) ∧
      (∀ j, ∃ i, c i = floorPower^[j] m) ∧
      (∀ i, c (p i) = floorPower (c i)) ∧ p.IsCycleOn Set.univ ∧
      c ⟨0, hL⟩ = m ∧ c ⟨L - 1, by omega⟩ = M := by
  obtain ⟨L, hL, c, p, hc, hmem, hcover, hstep, h0, hlast⟩ :=
    periodicExtrema_sorted_model (CubicReturn.periodicExtrema_of_orbit hk hp hbound hmax)
  have hper : Function.IsPeriodicPt floorPower k m := hp
  have hmem' : ∀ i, ∃ j < k, c i = floorPower^[j] m := by
    intro i
    obtain ⟨j, hj⟩ := hmem i
    exact ⟨j % k, Nat.mod_lt _ hk, hj.symm.trans (hper.iterate_mod_apply j).symm⟩
  refine ⟨L, hL, c, p, hc, hmem', fun j => hcover _ ⟨j, rfl⟩, hstep,
    rank_isCycleOn_of_connected c hc.injective p floorPower hstep ?_, h0, hlast⟩
  intro i j
  obtain ⟨a, ha, hai⟩ := hmem' i
  obtain ⟨b, _, hbj⟩ := hmem' j
  rw [hai, hbj]
  exact periodic_orbit_reachable hp ha


/-- Ordinary positive-period data supplies the reusable complete sorted witness. -/
theorem periodicOrbit_model {m M k : ℕ} (hk : 0 < k)
    (hp : floorPower^[k] m = m)
    (hbound : ∀ j < k, m ≤ floorPower^[j] m ∧ floorPower^[j] m ≤ M)
    (hmax : ∃ j < k, floorPower^[j] m = M) :
    Nonempty (PeriodicOrbitModel m M k) := by
  obtain ⟨L, hL, c, p, hc, hmem, hcover, hstep, hcycle, h0, hlast⟩ :=
    periodicOrbit_sorted_model hk hp hbound hmax
  exact ⟨⟨L, hL, c, p, hc, hmem, hcover, hstep, hcycle, h0, hlast, hk, hp⟩⟩

theorem image_oe_eq {x : ℕ} (h : follows x [.odd, .even]) :
    image x [.odd, .even] = ReturnCells.oe x := by
  simp only [image_cons, image_nil]
  rw [floorPower_even_eq h.2.1, floorPower_odd_eq h.1]
  rfl

theorem image_ooe_eq {x : ℕ} (h : follows x [.odd, .odd, .even]) :
    image x [.odd, .odd, .even] = ReturnCells.ooe x := by
  simp only [image_cons, image_nil]
  rw [floorPower_even_eq h.2.2.1, floorPower_odd_eq h.2.1, floorPower_odd_eq h.1]
  rfl

theorem image_oe_lt {x : ℕ} (hx : 3 ≤ x) (h : follows x [.odd, .even]) :
    image x [.odd, .even] < x := by
  rw [image_oe_eq h]
  have hcell := (ReturnCells.oe_cell x).1
  have hxpos : 0 < x ^ 3 := pow_pos (by omega) _
  have hxp : x ^ 3 < x ^ 4 := by
    have he : x ^ 4 = x ^ 3 * x := by ring
    nlinarith
  by_contra hn
  have hh := Nat.pow_le_pow_left (show x ≤ ReturnCells.oe x by omega) 4
  omega

theorem image_ooe_gt {x : ℕ} (hx : 5 ≤ x) (h : follows x [.odd, .odd, .even]) :
    x < image x [.odd, .odd, .even] := by
  rw [image_ooe_eq h]
  simpa [ReturnCells.ooe, ReturnCells.oe, CubicReturn.O] using CubicReturn.ooe_gt hx

/-- The OOE/OE section follows from actual one-letter rank branches. -/
theorem RankedReturn.ooe_oe_section {o e m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn o e y [.odd] [.even]) (ho : 0 < o) (he : 0 < e)
    (hm : 5 ≤ m) (hy : m ≤ y 0) :
    ∃ a b, 0 < a ∧ 0 < b ∧ o = 2 * a + b ∧ e = a + b ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i % 2 = 1) := by
  have heo : e < o := h.lt_of_concat_decreases hy ho (by
    intro x hx hf
    exact image_oe_lt (by omega) hf)
  have h₁ := h.left heo.le
  have hsmall : o - e < e := h₁.lt_of_concat_grows hy he (by
    intro x hx hf
    exact image_ooe_gt (by omega) hf)
  have h₂ := h₁.right hsmall.le
  refine ⟨o - e, e - (o - e), by omega, by omega, by omega, by omega, h₂, ?_⟩
  intro i hi
  exact (h.lower i (by omega)).1.1

/-- A harmless extension lets all induced prefixes keep the same rank function. -/
def extendRanks {L : ℕ} (c : Fin L → ℕ) (i : ℕ) : ℕ :=
  if hi : i < L then c ⟨i, hi⟩ else 0

theorem extendRanks_apply {L : ℕ} (c : Fin L → ℕ) (i : Fin L) :
    extendRanks c i.val = c i := by simp [extendRanks, i.isLt]

theorem rankStep_mod {a b i : ℕ} (hi : i < a + b) :
    ReturnInduction.rankStep a b i = (i + b) % (a + b) := by
  by_cases hia : i < a
  · simp [ReturnInduction.rankStep, hia, Nat.mod_eq_of_lt (show i + b < a + b by omega)]
  · have he : i + b = (i - a) + (a + b) := by omega
    have hi' : i - a < a + b := by omega
    simp [ReturnInduction.rankStep, hia, he, Nat.mod_eq_of_lt hi']

/-- Actual sorted cubic permutations supply all one-letter guards and rank equations. -/
theorem rankedReturn_of_sorted_cubic {m L o : ℕ} (ho : o ≤ L)
    (c : Fin L → ℕ) (hc : StrictMono c) (p : Equiv.Perm (Fin L))
    (hband : ∀ i, InCubicBand m (c i))
    (hcut : ∀ i, c i < m ^ 2 ↔ i.val < o)
    (hstep : ∀ i, c (p i) = floorPower (c i)) :
    RankedReturn o (L - o) (extendRanks c) [.odd] [.even] := by
  have hlen : o + (L - o) = L := Nat.add_sub_of_le ho
  have hrot := cubicBand_rank_rotation ho c hc p hband hcut hstep
  have hpar : ∀ i, c i % 2 = 1 ↔ i.val < o := by
    intro i
    have hn := cubicBand_parity_iff (hband i) (by simpa [hstep i] using hband (p i))
    exact hn.trans (hcut i)
  have hnext : ∀ i : Fin L,
      floorPower (c i) = extendRanks c (ReturnInduction.rankStep o (L - o) i.val) := by
    intro i
    rw [rankStep_mod (by simp [hlen]), hlen, ← hrot i]
    rw [extendRanks_apply, hstep]
  constructor
  · intro i j hij hj
    have hjL : j < L := by omega
    have hiL : i < L := by omega
    simpa only [extendRanks, dif_pos hiL, dif_pos hjL] using
      hc (show (⟨i, hiL⟩ : Fin L) < ⟨j, hjL⟩ from hij)
  · intro i hi
    have hiL : i < L := by omega
    let j : Fin L := ⟨i, hiL⟩
    have hj : extendRanks c i = c j := by simp [extendRanks, hiL, j]
    refine ⟨?_, ?_⟩
    · exact ⟨by rw [hj]; exact (hpar j).mpr hi, trivial⟩
    · simpa [image, hj, j, ReturnInduction.rankStep, hi] using hnext j
  · intro i hi hin
    have hiL : i < L := by omega
    let j : Fin L := ⟨i, hiL⟩
    have hj : extendRanks c i = c j := by simp [extendRanks, hiL, j]
    refine ⟨?_, ?_⟩
    · have hn : c j % 2 ≠ 1 := by
        intro hp
        have := (hpar j).mp hp
        change i < o at this
        omega
      exact ⟨by rw [hj]; omega, trivial⟩
    · simpa [image, hj, j, ReturnInduction.rankStep, show ¬i < o by omega] using hnext j

/-- The same complete sorted witness supplies the return section and all expanded counts. -/
theorem return_section_of_sorted {C : Set ℕ} {m M L : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3)
    (hL : 0 < L) (c : Fin L → ℕ) (p : Equiv.Perm (Fin L)) (hc : StrictMono c)
    (hcC : ∀ i, c i ∈ C) (hcover : ∀ x ∈ C, ∃ i, c i = x)
    (hstep : ∀ i, c (p i) = floorPower (c i))
    (hc0 : c ⟨0, hL⟩ = m) (hcLast : c ⟨L - 1, by omega⟩ = M) :
    ∃ a b y, 0 < a ∧ 0 < b ∧ y 0 = m ∧ y (a + b - 1) = M.sqrt ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i ∈ C ∧ y i % 2 = 1) ∧
      PrefixSection C (a + b) y ∧
      3 * a + 2 * b = L ∧
      2 * a + b = (Finset.univ.filter (fun i => c i % 2 = 1)).card ∧
      a + b = (Finset.univ.filter (fun i => c i % 2 = 0)).card ∧
      ((∀ x ∈ C, ∀ z ∈ C, ∃ k, floorPower^[k] x = z) → Nat.Coprime a b) := by
  classical
  obtain ⟨o, ho, hcut, hcard⟩ := sorted_threshold_cut c hc (t := m ^ 2)
  have hband : ∀ i, InCubicBand m (c i) := fun i => D.band hM (hcC i)
  have hthreshold : ∀ i, c (p i) = thresholdMap m (c i) := by
    intro i
    rw [hstep, D.normalized hM (hcC i)]
  obtain ⟨hop, hoL⟩ := threshold_branch_count_bounds (by omega) hL ho c hc p
    hband hcut hthreshold
  have hr := rankedReturn_of_sorted_cubic ho c hc p hband hcut hstep
  let y := extendRanks c
  have hyC : ∀ i, i < L → y i ∈ C := by
    intro i hi
    simpa [y, extendRanks, hi] using hcC ⟨i, hi⟩
  have hy0 : y 0 = m := by
    simpa [y, extendRanks, hL] using hc0
  have hyLast : y (L - 1) = M := by
    simpa [y, extendRanks, show L - 1 < L by omega] using hcLast
  obtain ⟨a, b, ha, hb, hoab, heab, hreturn, hodd⟩ :=
    hr.ooe_oe_section hop (by omega) hm (by simp [y, hy0])
  have hmaxstep := (hr.upper (L - 1) (by omega) (by omega)).2
  have hlast : y (a + b - 1) = M.sqrt := by
    change floorPower (y (L - 1)) = y (L - 1 - o) at hmaxstep
    rw [hyLast, floorPower_even_eq (D.max_even (by omega))] at hmaxstep
    have hi : L - 1 - o = a + b - 1 := by omega
    simpa [hi] using hmaxstep.symm
  have hfull : PrefixSection C L y := by
    refine ⟨hL, ?_, hyC, ?_⟩
    · intro i j hij hj
      exact hr.ordered i j hij (by omega)
    · intro x hx _
      obtain ⟨i, hi⟩ := hcover x hx
      exact ⟨i.val, i.isLt, (extendRanks_apply c i).trans hi⟩
  have hpar : ∀ i, c i % 2 = 1 ↔ c i < m ^ 2 := fun i => D.parity hM (hcC i)
  have hoddcard : (Finset.univ.filter (fun i => c i % 2 = 1)).card = o := by
    simpa only [hpar] using hcard
  have hevencard : (Finset.univ.filter (fun i => c i % 2 = 0)).card = L - o := by
    have heq : (Finset.univ.filter (fun i => c i % 2 = 0)) =
        Finset.univ.filter (fun i => ¬ c i % 2 = 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin L))) (fun i => c i % 2 = 1)
    rw [← heq, hoddcard] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  refine ⟨a, b, y, ha, hb, hy0, hlast, hreturn, ?_,
    hfull.restrict (by omega) (by omega), ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨hyC i (by omega), hodd i hi⟩
  · omega
  · omega
  · omega
  · intro hconnected
    have hpcycle := rank_isCycleOn_of_connected c hc.injective p floorPower hstep
      (fun i j => hconnected _ (hcC i) _ (hcC j))
    have hcLe := rankRotation_coprime hL p
      (cubicBand_rank_rotation ho c hc p hband hcut hstep) (by simpa using hpcycle)
    have hcLo := (Nat.coprime_self_sub_right ho).mp hcLe
    apply ReturnWordFactorization.InducedPair.initial.coprime_of_totals
      (L := L) (o := o) (a := a) (b := b) _ _ hcLo
    · norm_num
      omega
    · norm_num [oddCount]
      omega

/-- Sorting an actual bounded periodic set constructs the guarded return section. -/
theorem periodicExtrema_return_section {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3) :
    ∃ a b y, 0 < a ∧ 0 < b ∧ y 0 = m ∧ y (a + b - 1) = M.sqrt ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i ∈ C ∧ y i % 2 = 1) ∧
      PrefixSection C (a + b) y ∧
      ((∀ x ∈ C, ∀ z ∈ C, ∃ k, floorPower^[k] x = z) → Nat.Coprime a b) := by
  obtain ⟨L, hL, c, p, hc, hcC, hcover, hstep, h0, hlast⟩ :=
    periodicExtrema_sorted_model D
  obtain ⟨a, b, y, ha, hb, hy0, hylast, hr, hmem, hsection, _, _, _, hcop⟩ :=
    return_section_of_sorted D hm hM hL c p hc hcC hcover hstep h0 hlast
  exact ⟨a, b, y, ha, hb, hy0, hylast, hr, hmem, hsection, hcop⟩

/-- Compatibility interface for clients requiring only guarded return equations. -/
theorem periodicExtrema_return_model {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 3) :
    ∃ a b y, 0 < a ∧ 0 < b ∧ y 0 = m ∧ y (a + b - 1) = M.sqrt ∧
      RankedReturn a b y [.odd, .odd, .even] [.odd, .even] ∧
      (∀ i, i < a + b → y i ∈ C ∧ y i % 2 = 1) := by
  obtain ⟨a, b, y, ha, hb, h0, hlast, hr, hmem, _⟩ :=
    periodicExtrema_return_section D hm hM
  exact ⟨a, b, y, ha, hb, h0, hlast, hr, hmem⟩

end Problems.Juggler.ReturnSeams
