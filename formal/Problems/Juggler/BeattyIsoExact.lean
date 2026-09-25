import Problems.Juggler.BeattyIsoFrostman

/-!
# Exact Hausdorff dimension at isolated slopes

For `ν > 1`, put `γ* = ν + 2 - √(1+3ν)`. Every `s < s*(ν)` satisfies the two
exponent conditions of `BeattyIsoFrostman` at `γ*` with some `η > 0`. So an
isolated slope whose good levels admit a sparse enumeration has
`dim_H K_α ≥ s*(ν)`, and with the upper bound of `BeattySlopeIsolated`,
`dim_H K_α = s*(ν)`.

The explicit tower `g (l+1) = g l + 2 + (2 U_(g l + 1))^((l+2)²)`, with `U` the
denominators of the all-good slope, is such an enumeration. Hence for every
`ν > 1` some slope of Diophantine class `ν` has `dim_H K_α = s*(ν)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory

variable {ν : ℝ} {G : ℕ → Prop} [DecidablePred G]

/-- Denominators are largest when every index is good. -/
theorem isoDen_le_top (hν : 1 ≤ ν) : ∀ k, isoDen ν G k ≤ isoDen ν (fun _ => True) k
  | 0 => le_rfl
  | 1 => le_rfl
  | k + 2 => by
    have h1 := isoDen_le_top hν (k + 1)
    have h0 := isoDen_le_top hν k
    have ha : (if G (k + 1) then ⌈(isoDen ν G (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) ≤
        ⌈(isoDen ν (fun _ => True) (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1 := by
      split_ifs
      · have : (isoDen ν G (k + 1) : ℝ) ^ (ν - 1) ≤
            (isoDen ν (fun _ => True) (k + 1) : ℝ) ^ (ν - 1) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1) (by linarith)
        have := Nat.ceil_mono this
        omega
      · omega
    show (if G (k + 1) then _ else 1) * isoDen ν G (k + 1) + isoDen ν G k ≤
      (if True then _ else 1) * isoDen ν (fun _ => True) (k + 1) + isoDen ν (fun _ => True) k
    rw [if_pos trivial]
    exact Nat.add_le_add (Nat.mul_le_mul ha h1) h0

/-- Denominators grow at least linearly: `k ≤ Q_k + 1`. -/
theorem idx_le_isoDen : ∀ k, k ≤ isoDen ν G k + 1
  | 0 => by omega
  | 1 => by simp [isoDen]
  | k + 2 => by
    have ih := idx_le_isoDen (k + 1)
    have hA := isoDen_pos (ν := ν) (G := G) k
    have hsum : isoDen ν G (k + 1) + isoDen ν G k ≤ isoDen ν G (k + 2) := by
      show _ ≤ (if G (k + 1) then _ else 1) * isoDen ν G (k + 1) + isoDen ν G k
      split_ifs
      · have : isoDen ν G (k + 1) ≤ (⌈(isoDen ν G (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1) *
            isoDen ν G (k + 1) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      · omega
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; omega
    · have hB := isoDen_pos (ν := ν) (G := G) (k - 1)
      rw [show k - 1 + 1 = k by omega] at hB
      omega

namespace IsoLevels

variable {B : ℝ}

/-- Dropping the first `k` levels raises the size floor to `Q_(g k)`. -/
def shift (Lv : IsoLevels ν G B) (k : ℕ) (B' : ℝ) (hB : B' ≤ isoDen ν G (Lv.g k)) :
    IsoLevels ν G B' where
  g l := Lv.g (l + k)
  mono := Lv.mono.comp fun _ _ h => Nat.add_lt_add_right h _
  one_le := Lv.one_le_g _
  good_mem l := Lv.good_mem _
  gap l k' h1 h2 := Lv.gap (l + k) k' h1 (by rwa [show l + 1 + k = l + k + 1 by ring] at h2)
  big := by simpa using hB
  sparse l := by
    have hb : 1 ≤ (2 : ℝ) * isoDen ν G (Lv.g (l + k) + 1) := by
      have : (1 : ℝ) ≤ isoDen ν G (Lv.g (l + k) + 1) := by
        exact_mod_cast isoDen_pos (Lv.g (l + k))
      linarith
    calc ((2 : ℝ) * isoDen ν G (Lv.g (l + k) + 1)) ^ ((l + 2) ^ 2)
        ≤ ((2 : ℝ) * isoDen ν G (Lv.g (l + k) + 1)) ^ ((l + k + 2) ^ 2) :=
          pow_le_pow_right₀ hb (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ isoDen ν G (Lv.g (l + k + 1)) := Lv.sparse (l + k)
      _ = isoDen ν G (Lv.g (l + 1 + k)) := by rw [show l + 1 + k = l + k + 1 by ring]

/-- Any size floor is reached by dropping levels. -/
theorem raise (Lv : IsoLevels ν G B) (B' : ℝ) : Nonempty (IsoLevels ν G B') := by
  set k := ⌈B'⌉₊
  have hg : k + 1 ≤ Lv.g k := by
    have : ∀ n, n + 1 ≤ Lv.g n := by
      intro n
      induction n with
      | zero => exact Lv.one_le
      | succ n ih => have := Lv.mono (Nat.lt_add_one n); omega
    exact this k
  have h1 := idx_le_isoDen (ν := ν) (G := G) (Lv.g k)
  have : B' ≤ isoDen ν G (Lv.g k) := by
    have hk : B' ≤ k := Nat.le_ceil B'
    have : k ≤ isoDen ν G (Lv.g k) := by omega
    calc B' ≤ k := hk
      _ ≤ isoDen ν G (Lv.g k) := by exact_mod_cast this
  exact ⟨Lv.shift k B' this⟩

/-- Good indices exist beyond every bound. -/
theorem frequent (Lv : IsoLevels ν G B) : ∀ N, ∃ k, N ≤ k ∧ G (k + 1) := by
  intro N
  have : ∀ n, n + 1 ≤ Lv.g n := by
    intro n
    induction n with
    | zero => exact Lv.one_le
    | succ n ih => have := Lv.mono (Nat.lt_add_one n); omega
  refine ⟨Lv.g N - 1, by have := this N; omega, ?_⟩
  rw [show Lv.g N - 1 + 1 = Lv.g N by have := this N; omega]
  exact Lv.good N

end IsoLevels

/-- The optimal window exponent `γ* = ν + 2 - √(1+3ν)`. -/
noncomputable def isoGamma (ν : ℝ) : ℝ := ν + 2 - Real.sqrt (1 + 3 * ν)

/-- **Exponent choice.** For `ν > 1` and `0 < s < s*(ν)`: `1 < γ* < ν`,
`s < 2/3`, and some `η > 0` satisfies both exponent conditions at `γ*`. -/
theorem isoGamma_exponents (hν : 1 < ν) {s : ℝ} (hs : s < starDim ν) :
    1 < isoGamma ν ∧ isoGamma ν < ν ∧ s < 2 / 3 ∧ ∃ η : ℝ, 0 < η ∧
      isoGamma ν - 1 + η ≤ ν * (1 - 3 * s / 2) ∧
      s * (3 + ν - isoGamma ν) / 2 ≤ 1 - η := by
  set r := Real.sqrt (1 + 3 * ν) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 + 3 * ν := Real.sq_sqrt (by linarith)
  have hr_lt : r < ν + 1 := by nlinarith
  have hr_gt : 2 < r := by nlinarith
  have hstar : starDim ν = 2 * (r - 1) / (3 * ν) := rfl
  have h3ν : 0 < 3 * ν := by linarith
  -- `s* = 2/(r+1)`, since `(r-1)(r+1) = 3ν`
  have hstar' : starDim ν * (r + 1) = 2 := by
    rw [hstar, div_mul_eq_mul_div, div_eq_iff h3ν.ne']; nlinarith
  have hs23 : starDim ν < 2 / 3 := by
    rw [hstar, div_lt_iff₀ h3ν]; nlinarith
  refine ⟨by simp only [isoGamma]; linarith, by simp only [isoGamma]; linarith,
    hs.trans hs23, ?_⟩
  have hg : 3 + ν - isoGamma ν = r + 1 := by simp only [isoGamma]; ring
  set η₁ := (r - 1) - 3 * ν * s / 2
  set η₂ := 1 - s * (r + 1) / 2
  have hη₁ : 0 < η₁ := by
    have : 3 * ν * starDim ν / 2 = r - 1 := by
      rw [hstar]; field_simp
    have : 3 * ν * s / 2 < 3 * ν * starDim ν / 2 := by nlinarith
    simp only [η₁]; linarith
  have hη₂ : 0 < η₂ := by
    have : s * (r + 1) < starDim ν * (r + 1) := by nlinarith
    simp only [η₂]; linarith
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_, ?_⟩
  · have := min_le_left η₁ η₂
    simp only [isoGamma, η₁] at this ⊢; nlinarith
  · have := min_le_right η₁ η₂
    rw [hg]; simp only [η₂] at this; linarith

/-- A size floor meeting the parameter conditions at `γ`. -/
theorem exists_isoParams {γ : ℝ} (h1 : 1 < γ) (h2 : γ < ν) : ∃ B, IsoParams ν γ B := by
  set B := max 10 (max ((8 : ℝ) ^ (1 / (γ - 1))) ((5 : ℝ) ^ (1 / (ν - γ))))
  have hB10 : 10 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have key : ∀ (c e : ℝ), 0 < c → 0 < e → c ^ (1 / e) ≤ B →
      c ≤ B ^ e := fun c e hc he h => by
    calc c = (c ^ (1 / e)) ^ e := by
          rw [← Real.rpow_mul hc.le, one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ B ^ e := Real.rpow_le_rpow (by positivity) h he.le
  exact ⟨B, h1, h2, hB10,
    key 8 _ (by norm_num) (by linarith) ((le_max_left _ _).trans (le_max_right _ _)),
    key 5 _ (by norm_num) (by linarith) ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- **Lower bound.** An isolated slope whose good levels admit a sparse
enumeration has `dim_H K_α ≥ s*(ν)`. -/
theorem iso_dimH_ge {B : ℝ} (Lv : IsoLevels ν G B) (hν : 1 < ν) :
    ENNReal.ofReal (starDim ν) ≤ dimH (passageClusterSet (1 / isoSlope ν G)) := by
  have hmain : ∀ s, 0 < s → s < starDim ν →
      ENNReal.ofReal s ≤ dimH (passageClusterSet (1 / isoSlope ν G)) := by
    intro s hs hss
    obtain ⟨hγ1, hγν, hs23, η, hη, hE1, hE2⟩ := isoGamma_exponents hν hss
    obtain ⟨B', P⟩ := exists_isoParams hγ1 hγν
    obtain ⟨Lv'⟩ := Lv.raise B'
    have hne := IsoLevels.hausdorff_ne_zero P Lv' hs hs23 hη hE1 hE2
    have : ((s.toNNReal : NNReal) : ℝ) = s := Real.coe_toNNReal _ hs.le
    rw [← this] at hne
    exact le_dimH_of_hausdorffMeasure_ne_zero hne
  apply le_of_forall_lt
  intro c hc
  have hcT : c ≠ ⊤ := ne_top_of_lt hc
  have hc' : c.toReal < starDim ν := by
    rw [← ENNReal.ofReal_toReal hcT] at hc
    exact (ENNReal.ofReal_lt_ofReal_iff (starDim_pos (by linarith))).1 hc
  obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hc' (starDim_pos (by linarith : (0 : ℝ) < ν)))
  have hs0 : 0 < s := (le_max_right _ _).trans_lt hs1
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hcT).symm
    _ < ENNReal.ofReal s :=
        (ENNReal.ofReal_lt_ofReal_iff hs0).2 ((le_max_left _ _).trans_lt hs1)
    _ ≤ _ := hmain s hs0 hs2

/-- **Exact dimension.** An isolated slope whose good levels admit a sparse
enumeration has `dim_H K_α = s*(ν)`. -/
theorem iso_dimH_eq {B : ℝ} (Lv : IsoLevels ν G B) (hν : 1 < ν) :
    dimH (passageClusterSet (1 / isoSlope ν G)) = ENNReal.ofReal (starDim ν) :=
  le_antisymm (isoSlope_dims hν Lv.frequent).2 (iso_dimH_ge Lv hν)

/-- The tower of good indices: `g 0 = 1`, `g (l+1) = g l + 2 + (2 U_(g l + 1))^((l+2)²)`. -/
noncomputable def isoTower (ν : ℝ) : ℕ → ℕ
  | 0 => 1
  | l + 1 => isoTower ν l + 2 + (2 * isoDen ν (fun _ => True) (isoTower ν l + 1)) ^ ((l + 2) ^ 2)

/-- The tower set of good indices. -/
def IsoTowerGood (ν : ℝ) (k : ℕ) : Prop := ∃ l, isoTower ν l = k

open Classical in
/-- The tower enumeration is a sparse enumeration of its good set. -/
noncomputable def isoTowerLevels (hν : 1 ≤ ν) : IsoLevels ν (IsoTowerGood ν) 1 where
  g := isoTower ν
  mono := strictMono_nat_of_lt_succ fun l => by simp only [isoTower]; omega
  one_le := le_rfl
  good_mem l := ⟨l, rfl⟩
  gap l k h1 h2 := by
    rintro ⟨l', rfl⟩
    have hm : StrictMono (isoTower ν) :=
      strictMono_nat_of_lt_succ fun l => by simp only [isoTower]; omega
    have a := hm.lt_iff_lt.1 h1
    have b := hm.lt_iff_lt.1 h2
    omega
  big := by simp [isoTower, isoDen]
  sparse l := by
    have hU := isoDen_le_top (G := IsoTowerGood ν) hν (isoTower ν l + 1)
    have hidx := idx_le_isoDen (ν := ν) (G := IsoTowerGood ν) (isoTower ν (l + 1))
    have hpow : (2 * isoDen ν (IsoTowerGood ν) (isoTower ν l + 1)) ^ ((l + 2) ^ 2) ≤
        (2 * isoDen ν (fun _ => True) (isoTower ν l + 1)) ^ ((l + 2) ^ 2) :=
      Nat.pow_le_pow_left (by omega) _
    have htow : isoTower ν (l + 1) =
        isoTower ν l + 2 + (2 * isoDen ν (fun _ => True) (isoTower ν l + 1)) ^ ((l + 2) ^ 2) :=
      rfl
    have : (2 * isoDen ν (IsoTowerGood ν) (isoTower ν l + 1)) ^ ((l + 2) ^ 2) ≤
        isoDen ν (IsoTowerGood ν) (isoTower ν (l + 1)) := by omega
    exact_mod_cast this

open Classical in
/-- **Isolated slopes of every class attain `s*(ν)`.** For every `ν > 1` the
tower slope has Diophantine class `ν`, law dimension `2/(2+ν)`, and cluster-set
Hausdorff dimension exactly `s*(ν)`. -/
theorem isoTower_dims (hν : 1 < ν) :
    DiophClass (isoSlope ν (IsoTowerGood ν)) ν ∧
    lawDimH (passageLaw (β := 1 / isoSlope ν (IsoTowerGood ν))
      (one_div_pos.2 (by linarith [one_lt_isoSlope ν (IsoTowerGood ν)]))
      ((div_lt_one (by linarith [one_lt_isoSlope ν (IsoTowerGood ν)])).2
        (one_lt_isoSlope ν (IsoTowerGood ν)))
      (by simpa using (isoSlope_irrational ν (IsoTowerGood ν)).inv) : Measure ℝ) =
      ENNReal.ofReal (2 / (2 + ν)) ∧
    dimH (passageClusterSet (1 / isoSlope ν (IsoTowerGood ν))) = ENNReal.ofReal (starDim ν) := by
  have Lv := isoTowerLevels hν.le
  exact ⟨isoSlope_diophClass hν Lv.frequent, (isoSlope_dims hν Lv.frequent).1,
    iso_dimH_eq Lv hν⟩

end Problems.Juggler.BeattySlope
