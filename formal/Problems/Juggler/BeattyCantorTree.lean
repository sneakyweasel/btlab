import Problems.Juggler.BeattySlopeFrostman

/-!
# Cantor distribution functions from window trees

A window tree has a root window `[0, d₀]` and, for each level `l`, gives every
window of length `d l` with left end `a` exactly `N l` children of length
`d (l+1)`, with left ends `child0 l a + m · sp l`, `m < N l`, lying inside the
parent and spaced by `sp l > d (l+1)`. Masses split equally:
`M (l+1) = M l / N l`.

The distribution functions `depth n l a` of depth `n` put mass `M (l+n)` uniformly
on each depth-`n` descendant window. They are continuous and nondecreasing,
vanish left of the window and equal `M l` right of it, and consecutive depths
differ by at most `M (l+n)`. Their limit `h` is a continuous nondecreasing
function with `h 0 = 0` and `h d₀ = 1`.

**Descent.** Let `Φ u v ≥ 0` be monotone under shrinking the interval. Suppose
every interval inside a charged window that meets at least two of its
children satisfies `M (l+1) ((v-u)/sp l + 2) ≤ C Φ(u,v)^s`. Then
`h v - h u ≤ C Φ(u,v)^s` for every interval. An interval meeting no child has
zero increment. An interval meeting exactly one child can be cut down to that
child's window without changing its increment, and the descent ends because
the masses `M l` tend to zero.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set

/-- A tree of windows on the line. -/
structure WindowTree where
  /-- Number of children of a level-`l` window. -/
  N : ℕ → ℕ
  /-- Length of a level-`l` window. -/
  d : ℕ → ℝ
  /-- Spacing of the children of a level-`l` window. -/
  sp : ℕ → ℝ
  /-- Left end of the first child of the level-`l` window with left end `a`. -/
  child0 : ℕ → ℝ → ℝ
  two_le_N : ∀ l, 2 ≤ N l
  d_pos : ∀ l, 0 < d l
  d_lt_sp : ∀ l, d (l + 1) < sp l
  child0_ge : ∀ l a, a ≤ child0 l a
  last_le : ∀ l a, child0 l a + ((N l : ℝ) - 1) * sp l + d (l + 1) ≤ a + d l

namespace WindowTree

variable (T : WindowTree)

/-- The `m`-th child's left end. -/
noncomputable def child (l : ℕ) (a : ℝ) (m : ℕ) : ℝ := T.child0 l a + m * T.sp l

/-- Masses: `M 0 = 1` and `M (l+1) = M l / N l`. -/
noncomputable def mass : ℕ → ℝ
  | 0 => 1
  | l + 1 => mass l / T.N l

/-- The clamp `min (max x 0) D`. -/
noncomputable def clampW (x D : ℝ) : ℝ := max 0 (min x D)

/-- Depth-`n` distribution function of the subtree of the level-`l` window at `a`. -/
noncomputable def depth : ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, l, a, t => T.mass l / T.d l * clampW (t - a) (T.d l)
  | n + 1, l, a, t => ∑ m ∈ Finset.range (T.N l), depth n (l + 1) (T.child l a m) t

/-- Charged windows: the root at `0`, and the children of charged windows. -/
def Charged : ℕ → ℝ → Prop
  | 0, a => a = 0
  | l + 1, a' => ∃ a m, Charged l a ∧ m < T.N l ∧ a' = T.child l a m

/-- Child spacings are positive. -/
theorem sp_pos (l : ℕ) : 0 < T.sp l := (T.d_pos (l + 1)).trans (T.d_lt_sp l)

/-- Children counts are positive. -/
theorem nChildren_pos (l : ℕ) : (0 : ℝ) < T.N l := by
  have := T.two_le_N l; exact_mod_cast (show 0 < T.N l by omega)

/-- Masses are positive. -/
theorem mass_pos : ∀ l, 0 < T.mass l
  | 0 => one_pos
  | l + 1 => div_pos (mass_pos l) (T.nChildren_pos l)

/-- A window mass is shared equally by its children. -/
theorem mass_succ (l : ℕ) : T.mass (l + 1) * T.N l = T.mass l := by
  simp only [mass]; field_simp [(T.nChildren_pos l).ne']

/-- A child mass is at most half the parent mass. -/
theorem mass_succ_le (l : ℕ) : T.mass (l + 1) ≤ T.mass l / 2 := by
  simp only [mass]
  have h2 : (2 : ℝ) ≤ T.N l := by exact_mod_cast T.two_le_N l
  exact div_le_div_of_nonneg_left (T.mass_pos l).le (by norm_num) h2

/-- Masses at least halve at each level. -/
theorem mass_le_pow (l n : ℕ) : T.mass (l + n) ≤ T.mass l * (1/2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc T.mass (l + (n + 1)) = T.mass (l + n + 1) := by ring_nf
      _ ≤ T.mass (l + n) / 2 := T.mass_succ_le _
      _ ≤ T.mass l * (1/2) ^ n / 2 := by linarith
      _ = T.mass l * (1/2) ^ (n + 1) := by ring

/-- Masses tend to zero along the levels. -/
theorem mass_tendsto (l : ℕ) : Tendsto (fun n => T.mass (l + n)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num)).const_mul (T.mass l)
  rw [mul_zero] at h
  exact squeeze_zero (fun n => (T.mass_pos _).le) (T.mass_le_pow l) h

/-- The clamp is nondecreasing. -/
theorem clampW_mono (D : ℝ) : Monotone fun x => clampW x D :=
  fun _ _ h => max_le_max le_rfl (min_le_min h le_rfl)

/-- The clamp is continuous. -/
theorem clampW_cont (D : ℝ) : Continuous fun x => clampW x D :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The clamp vanishes below zero. -/
theorem clampW_of_le {x D : ℝ} (h : x ≤ 0) (hD : 0 ≤ D) : clampW x D = 0 := by
  unfold clampW; rw [min_eq_left (h.trans hD)]; exact max_eq_left h

/-- The clamp equals `D` above `D`. -/
theorem clampW_of_ge {x D : ℝ} (h : D ≤ x) (hD : 0 ≤ D) : clampW x D = D := by
  unfold clampW; rw [min_eq_right h]; exact max_eq_right hD

/-- The children lie inside the parent, spaced by `sp`. -/
theorem child_ge (l : ℕ) (a : ℝ) (m : ℕ) : a ≤ T.child l a m := by
  unfold child
  have := T.child0_ge l a
  have : 0 ≤ (m : ℝ) * T.sp l := mul_nonneg (Nat.cast_nonneg m) (T.sp_pos l).le
  linarith

/-- Every child window ends inside its parent. -/
theorem child_end_le (l : ℕ) (a : ℝ) {m : ℕ} (hm : m < T.N l) :
    T.child l a m + T.d (l + 1) ≤ a + T.d l := by
  unfold child
  have h := T.last_le l a
  have hm' : (m : ℝ) ≤ (T.N l : ℝ) - 1 := by
    have : m + 1 ≤ T.N l := hm
    have : ((m + 1 : ℕ) : ℝ) ≤ T.N l := by exact_mod_cast this
    push_cast at this; linarith
  nlinarith [T.sp_pos l]

/-- Depth-`n` functions are monotone and continuous, vanish left of the
window and equal the window mass right of it. -/
theorem depth_props : ∀ n l a, Monotone (T.depth n l a) ∧ Continuous (T.depth n l a) ∧
    (∀ t, t ≤ a → T.depth n l a t = 0) ∧ (∀ t, a + T.d l ≤ t → T.depth n l a t = T.mass l)
  | 0, l, a => by
    have hc : 0 ≤ T.mass l / T.d l := div_nonneg (T.mass_pos l).le (T.d_pos l).le
    refine ⟨fun x y hxy => ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [depth]
      exact mul_le_mul_of_nonneg_left (clampW_mono _ (by linarith)) hc
    · simp only [depth]
      exact continuous_const.mul ((clampW_cont _).comp (continuous_id.sub continuous_const))
    · simp only [depth]; rw [clampW_of_le (by linarith) (T.d_pos l).le, mul_zero]
    · simp only [depth]; rw [clampW_of_ge (by linarith) (T.d_pos l).le]
      field_simp [(T.d_pos l).ne']
  | n + 1, l, a => by
    have ih := fun m => depth_props n (l + 1) (T.child l a m)
    refine ⟨fun x y hxy => ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
    · simp only [depth]
      exact Finset.sum_le_sum fun m _ => (ih m).1 hxy
    · simp only [depth]
      exact continuous_finsetSum _ fun m _ => (ih m).2.1
    · simp only [depth]
      exact Finset.sum_eq_zero fun m _ => (ih m).2.2.1 t (ht.trans (T.child_ge l a m))
    · simp only [depth]
      rw [Finset.sum_congr rfl fun m hm => (ih m).2.2.2 t
        ((T.child_end_le l a (Finset.mem_range.1 hm)).trans ht)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm, T.mass_succ]

/-- Depth functions are nonnegative. -/
theorem depth_nonneg (n l : ℕ) (a t : ℝ) : 0 ≤ T.depth n l a t := by
  obtain ⟨hm, -, h0, -⟩ := T.depth_props n l a
  rcases le_total t a with h | h
  · rw [h0 t h]
  · rw [← h0 a le_rfl]; exact hm h

/-- Depth functions are at most the window mass. -/
theorem depth_le (n l : ℕ) (a t : ℝ) : T.depth n l a t ≤ T.mass l := by
  obtain ⟨hm, -, -, h1⟩ := T.depth_props n l a
  rcases le_total t (a + T.d l) with h | h
  · rw [← h1 (a + T.d l) le_rfl]; exact hm h
  · rw [h1 t h]

/-- A point lies in at most one child window. -/
theorem child_unique (l : ℕ) (a t : ℝ) {m m' : ℕ} (h1 : T.child l a m < t)
    (h2 : t < T.child l a m + T.d (l + 1)) (h1' : T.child l a m' < t)
    (h2' : t < T.child l a m' + T.d (l + 1)) : m = m' := by
  unfold child at *
  have hsp := T.sp_pos l
  have hd := T.d_lt_sp l
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
    nlinarith
  · have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
    nlinarith

/-- Consecutive depths differ by at most `M (l+n)`. -/
theorem depth_step : ∀ n l a t, |T.depth (n + 1) l a t - T.depth n l a t| ≤ T.mass (l + n)
  | 0, l, a, t => by
    rw [abs_le]
    have := T.depth_nonneg 1 l a t
    have := T.depth_le 1 l a t
    have := T.depth_nonneg 0 l a t
    have := T.depth_le 0 l a t
    simp only [add_zero]
    constructor <;> linarith
  | n + 1, l, a, t => by
    classical
    have hsum : T.depth (n + 1 + 1) l a t - T.depth (n + 1) l a t =
        ∑ m ∈ Finset.range (T.N l),
          (T.depth (n + 1) (l + 1) (T.child l a m) t - T.depth n (l + 1) (T.child l a m) t) := by
      simp only [depth]; rw [Finset.sum_sub_distrib]
    rw [hsum]
    -- terms vanish outside the child window
    have hzero (m : ℕ) (hm : ¬ (T.child l a m < t ∧ t < T.child l a m + T.d (l + 1))) :
        T.depth (n + 1) (l + 1) (T.child l a m) t - T.depth n (l + 1) (T.child l a m) t = 0 := by
      have p1 := T.depth_props (n + 1) (l + 1) (T.child l a m)
      have p0 := T.depth_props n (l + 1) (T.child l a m)
      rcases not_and_or.1 hm with h | h
      · push Not at h; rw [p1.2.2.1 t h, p0.2.2.1 t h, sub_zero]
      · push Not at h; rw [p1.2.2.2 t h, p0.2.2.2 t h, sub_self]
    have hbound : ∀ m, |T.depth (n + 1) (l + 1) (T.child l a m) t -
        T.depth n (l + 1) (T.child l a m) t| ≤ T.mass (l + (n + 1)) := fun m => by
      have := depth_step n (l + 1) (T.child l a m) t
      rwa [show l + 1 + n = l + (n + 1) by ring] at this
    by_cases hex : ∃ m ∈ Finset.range (T.N l),
        T.child l a m < t ∧ t < T.child l a m + T.d (l + 1)
    · obtain ⟨m0, hm0, hin⟩ := hex
      rw [Finset.sum_eq_single_of_mem m0 hm0 fun m _ hne => hzero m fun h =>
        hne (T.child_unique l a t h.1 h.2 hin.1 hin.2)]
      exact hbound m0
    · push Not at hex
      rw [Finset.sum_eq_zero fun m hm => hzero m fun h => by
        have := hex m hm h.1; linarith [h.2]]
      simp only [abs_zero]; exact (T.mass_pos _).le

/-- The increment of a depth-`(n+1)` function over `[u, v]` is at most the
child mass times the number of children meeting `(u, v)`. -/
theorem depth_inc_le (n l : ℕ) (a : ℝ) {u v : ℝ} (huv : u ≤ v) :
    T.depth (n + 1) l a v - T.depth (n + 1) l a u ≤
      T.mass (l + 1) * ((Finset.range (T.N l)).filter
        (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))).card := by
  classical
  simp only [depth]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not (Finset.range (T.N l))
    (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))]
  have h2 : ∑ m ∈ (Finset.range (T.N l)).filter
      (fun m => ¬ (T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))),
      (T.depth n (l + 1) (T.child l a m) v - T.depth n (l + 1) (T.child l a m) u) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    have p := T.depth_props n (l + 1) (T.child l a m)
    rcases not_and_or.1 hm' with h | h
    · push Not at h; rw [p.2.2.1 v h, p.2.2.1 u (huv.trans h), sub_self]
    · push Not at h; rw [p.2.2.2 u h, p.2.2.2 v (h.trans huv), sub_self]
  rw [h2, add_zero]
  calc ∑ m ∈ _, (T.depth n (l + 1) (T.child l a m) v - T.depth n (l + 1) (T.child l a m) u)
      ≤ ∑ m ∈ (Finset.range (T.N l)).filter
          (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1)), T.mass (l + 1) := by
        refine Finset.sum_le_sum fun m _ => ?_
        linarith [T.depth_le n (l + 1) (T.child l a m) v, T.depth_nonneg n (l + 1) (T.child l a m) u]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- At most `(v - u)/sp + 2` children meet `(u, v)`. -/
theorem card_meet_le (l : ℕ) (a : ℝ) {u v : ℝ} (huv : u ≤ v) :
    ((((Finset.range (T.N l)).filter
      (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))).card : ℕ) : ℝ) ≤
      (v - u) / T.sp l + 2 := by
  classical
  set S := (Finset.range (T.N l)).filter
    (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty, Nat.cast_zero]
    have := T.sp_pos l
    have : 0 ≤ (v - u) / T.sp l := div_nonneg (by linarith) this.le
    linarith
  set m0 := S.min' hS
  have hsp := T.sp_pos l
  have hd := T.d_lt_sp l
  have hm0 := (Finset.mem_filter.1 (S.min'_mem hS)).2
  set K := ⌊(v - u) / T.sp l⌋₊ + 1
  have hsub : S ⊆ Finset.Icc m0 (m0 + K) := by
    intro m hm
    have hmS := (Finset.mem_filter.1 hm).2
    refine Finset.mem_Icc.2 ⟨S.min'_le m hm, ?_⟩
    unfold child at hmS hm0
    have hdiff : ((m : ℝ) - m0) * T.sp l < v - u + T.sp l := by nlinarith [T.d_pos (l + 1)]
    have hlt : (m : ℝ) - m0 < (v - u) / T.sp l + 1 := by
      rw [div_add_one hsp.ne', lt_div_iff₀ hsp]; linarith
    have hfl : (v - u) / T.sp l < ⌊(v - u) / T.sp l⌋₊ + 1 := Nat.lt_floor_add_one _
    have : (m : ℝ) < m0 + K + 1 := by push_cast [K]; linarith
    have : m < m0 + K + 1 := by exact_mod_cast this
    omega
  calc (S.card : ℝ) ≤ ((Finset.Icc m0 (m0 + K)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = K + 1 := by rw [Nat.card_Icc, show m0 + K + 1 - m0 = K + 1 by omega]; push_cast; ring
    _ ≤ (v - u) / T.sp l + 2 := by
        have : (⌊(v - u) / T.sp l⌋₊ : ℝ) ≤ (v - u) / T.sp l :=
          Nat.floor_le (div_nonneg (by linarith) hsp.le)
        push_cast [K]; linarith

/-- **Localization.** Inside a charged window the root functions increase
exactly as the window's own subtree functions. -/
theorem depth_local : ∀ l a, T.Charged l a → ∀ n u v, a ≤ u → u ≤ v → v ≤ a + T.d l →
    T.depth (l + n) 0 0 v - T.depth (l + n) 0 0 u = T.depth n l a v - T.depth n l a u
  | 0, a, ha, n, u, v, _, _, _ => by
    have ha0 : a = 0 := ha
    subst ha0; rw [zero_add]
  | l + 1, a', ha', n, u, v, hu, huv, hv => by
    obtain ⟨a, m, ha, hm, rfl⟩ := ha'
    have hin := T.child_end_le l a hm
    have hge := T.child_ge l a m
    have ih := depth_local l a ha (n + 1) u v (by linarith) huv (by linarith)
    rw [show l + 1 + n = l + (n + 1) by ring, ih]
    simp only [depth]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem m (Finset.mem_range.2 hm)]
    intro m' _ hne
    have p := T.depth_props n (l + 1) (T.child l a m')
    have hsp := T.sp_pos l
    have hd := T.d_lt_sp l
    unfold child at hu hv p ⊢
    rcases lt_or_gt_of_ne hne with h | h
    · have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
      have hr : T.child0 l a + m' * T.sp l + T.d (l + 1) ≤ u := by nlinarith
      rw [p.2.2.2 v (hr.trans huv), p.2.2.2 u hr, sub_self]
    · have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
      have hl : v ≤ T.child0 l a + m' * T.sp l := by nlinarith
      rw [p.2.2.1 v hl, p.2.2.1 u (huv.trans hl), sub_self]

/-- Masses are summable. -/
theorem mass_summable : Summable T.mass := by
  refine Summable.of_nonneg_of_le (fun n => (T.mass_pos n).le) (fun n => ?_)
    (summable_geometric_two)
  have := T.mass_le_pow 0 n
  rw [zero_add, show T.mass 0 = 1 from rfl, one_mul] at this
  exact this

/-- The limit distribution function. -/
noncomputable def hlim (t : ℝ) : ℝ :=
  T.depth 0 0 0 t + ∑' n, (T.depth (n + 1) 0 0 t - T.depth n 0 0 t)

/-- Consecutive root depth functions differ summably. -/
theorem step_summable (t : ℝ) : Summable fun n => T.depth (n + 1) 0 0 t - T.depth n 0 0 t :=
  T.mass_summable.of_norm_bounded fun n => by
    simpa [Real.norm_eq_abs] using T.depth_step n 0 0 t

/-- The root depth functions converge to the limit distribution function. -/
theorem depth_tendsto (t : ℝ) : Tendsto (fun n => T.depth n 0 0 t) atTop (𝓝 (T.hlim t)) := by
  have h := (T.step_summable t).hasSum.tendsto_sum_nat
  have he (n : ℕ) : ∑ k ∈ Finset.range n, (T.depth (k + 1) 0 0 t - T.depth k 0 0 t) =
      T.depth n 0 0 t - T.depth 0 0 0 t := Finset.sum_range_sub (fun k => T.depth k 0 0 t) n
  simp only [he] at h
  have := h.const_add (T.depth 0 0 0 t)
  simp only [add_sub_cancel] at this
  exact this

/-- The limit distribution function is nondecreasing. -/
theorem hlim_mono : Monotone T.hlim := fun x y hxy =>
  le_of_tendsto_of_tendsto' (T.depth_tendsto x) (T.depth_tendsto y)
    fun n => (T.depth_props n 0 0).1 hxy

/-- The limit distribution function is continuous. -/
theorem hlim_cont : Continuous T.hlim := by
  unfold hlim
  refine ((T.depth_props 0 0 0).2.1).add (continuous_tsum (fun n =>
    ((T.depth_props (n + 1) 0 0).2.1).sub ((T.depth_props n 0 0).2.1)) T.mass_summable ?_)
  intro n t
  simpa [Real.norm_eq_abs] using T.depth_step n 0 0 t

/-- The limit distribution function vanishes at zero. -/
theorem hlim_zero : T.hlim 0 = 0 :=
  tendsto_nhds_unique (T.depth_tendsto 0)
    (tendsto_const_nhds.congr fun n => ((T.depth_props n 0 0).2.2.1 0 le_rfl).symm)

/-- The limit distribution function equals one at the end of the root window. -/
theorem hlim_top : T.hlim (T.d 0) = 1 :=
  tendsto_nhds_unique (T.depth_tendsto _)
    (tendsto_const_nhds.congr fun n => by
      rw [(T.depth_props n 0 0).2.2.2 _ (by simp)]; rfl)

/-- Increments of the limit inside a charged window are limits of the
window's own subtree increments. -/
theorem hlim_inc_tendsto {l : ℕ} {a : ℝ} (ha : T.Charged l a) {u v : ℝ} (hu : a ≤ u)
    (huv : u ≤ v) (hv : v ≤ a + T.d l) :
    Tendsto (fun n => T.depth n l a v - T.depth n l a u) atTop (𝓝 (T.hlim v - T.hlim u)) := by
  have h := ((T.depth_tendsto v).sub (T.depth_tendsto u)).comp (tendsto_add_atTop_nat l)
  refine h.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [add_comm n l]
  exact T.depth_local l a ha n u v hu huv hv

/-- **Descent.** If every interval inside a charged window meeting at least two
children satisfies the Frostman inequality at the child level, then every
interval of the root satisfies it. -/
theorem descent {Φ : ℝ → ℝ → ℝ} {C s : ℝ} (hC : 0 ≤ C) (hs : 0 < s)
    (hΦ0 : ∀ u v, u < v → 0 ≤ Φ u v)
    (hΦmono : ∀ u v u' v', u ≤ u' → u' < v' → v' ≤ v → Φ u' v' ≤ Φ u v)
    (hkey : ∀ l a u v, T.Charged l a → a ≤ u → u < v → v ≤ a + T.d l →
      2 ≤ ((Finset.range (T.N l)).filter
        (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1))).card →
      T.mass (l + 1) * ((v - u) / T.sp l + 2) ≤ C * Φ u v ^ s) :
    ∀ u v, 0 ≤ u → u < v → v ≤ T.d 0 → T.hlim v - T.hlim u ≤ C * Φ u v ^ s := by
  classical
  -- the descent with a remainder `M (l + k)`
  have hP : ∀ k l a u v, T.Charged l a → a ≤ u → u < v → v ≤ a + T.d l →
      T.hlim v - T.hlim u ≤ max (C * Φ u v ^ s) (T.mass (l + k)) := by
    intro k
    induction k with
    | zero =>
      intro l a u v ha hu huv hv
      refine le_trans ?_ (le_max_right _ _)
      refine le_of_tendsto (T.hlim_inc_tendsto ha hu huv.le hv) (Eventually.of_forall fun n => ?_)
      simp only [add_zero]
      linarith [T.depth_le n l a v, T.depth_nonneg n l a u]
    | succ k ih =>
      intro l a u v ha hu huv hv
      set S := (Finset.range (T.N l)).filter
        (fun m => T.child l a m < v ∧ u < T.child l a m + T.d (l + 1)) with hSdef
      have hlimit : T.hlim v - T.hlim u ≤ T.mass (l + 1) * S.card := by
        have ht := (T.hlim_inc_tendsto ha hu huv.le hv).comp (tendsto_add_atTop_nat 1)
        exact le_of_tendsto ht (Eventually.of_forall fun n => T.depth_inc_le n l a huv.le)
      have hX : 0 ≤ C * Φ u v ^ s := mul_nonneg hC (Real.rpow_nonneg (hΦ0 u v huv) s)
      rcases lt_or_ge S.card 2 with hlt | hge
      · rcases (show S.card = 0 ∨ S.card = 1 by omega) with h0 | h1
        · rw [h0, Nat.cast_zero, mul_zero] at hlimit
          exact hlimit.trans (le_trans hX (le_max_left _ _))
        · -- exactly one child meets `(u, v)`: cut down to it
          obtain ⟨m0, hm0⟩ := Finset.card_eq_one.1 h1
          have hmem : m0 ∈ S := by rw [hm0]; exact Finset.mem_singleton_self m0
          have hmem' := Finset.mem_filter.1 hmem
          have hm0N : m0 < T.N l := Finset.mem_range.1 hmem'.1
          have hlt1 := hmem'.2.1
          have hlt2 := hmem'.2.2
          set c := T.child l a m0
          have hcge := T.child_ge l a m0
          have hcend := T.child_end_le l a hm0N
          set u' := max u c
          set v' := min v (c + T.d (l + 1))
          have hu'v' : u' < v' := by
            simp only [u', v']
            exact max_lt (lt_min huv (by linarith)) (lt_min hlt1 (by linarith [T.d_pos (l + 1)]))
          -- no child meets the two cut-off pieces
          have hnone (x y : ℝ) (hx : u ≤ x) (hxy : x ≤ y) (hy : y ≤ v)
              (hout : y ≤ c ∨ c + T.d (l + 1) ≤ x) : T.hlim y - T.hlim x ≤ 0 := by
            have hS0 : ((Finset.range (T.N l)).filter
                (fun m => T.child l a m < y ∧ x < T.child l a m + T.d (l + 1))).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro m hm hmeet
              have hmS : m ∈ S := Finset.mem_filter.2 ⟨hm, by
                constructor <;> linarith [hmeet.1, hmeet.2]⟩
              rw [hm0, Finset.mem_singleton] at hmS
              subst hmS
              rcases hout with h | h <;> linarith [hmeet.1, hmeet.2]
            have ht := (T.hlim_inc_tendsto ha (hu.trans hx) hxy (hy.trans hv)).comp
              (tendsto_add_atTop_nat 1)
            refine le_of_tendsto ht (Eventually.of_forall fun n => ?_)
            have := T.depth_inc_le n l a hxy
            rw [hS0, Nat.cast_zero, mul_zero] at this
            exact this
          have hmono := T.hlim_mono
          have e1 : T.hlim v - T.hlim v' ≤ 0 := by
            rcases le_total v (c + T.d (l + 1)) with h | h
            · simp only [v', min_eq_left h, sub_self, le_refl]
            · have hv' : v' = c + T.d (l + 1) := min_eq_right h
              exact hnone v' v (by rw [hv']; linarith) (by rw [hv']; exact h) le_rfl
                (Or.inr (by rw [hv']))
          have e2 : T.hlim u' - T.hlim u ≤ 0 := by
            rcases le_total c u with h | h
            · simp only [u', max_eq_left h, sub_self, le_refl]
            · have hu' : u' = c := max_eq_right h
              have hvv : v' ≤ v := min_le_left _ _
              exact hnone u u' le_rfl (by rw [hu']; exact h) (by linarith [hu'v'.le])
                (Or.inl (by rw [hu']))
          have hch : T.Charged (l + 1) c := ⟨a, m0, ha, hm0N, rfl⟩
          have hrec := ih (l + 1) c u' v' hch (le_max_right _ _) hu'v' (min_le_right _ _)
          have hΦ := hΦmono u v u' v' (le_max_left _ _) hu'v' (min_le_left _ _)
          have hpow : C * Φ u' v' ^ s ≤ C * Φ u v ^ s :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hΦ0 u' v' hu'v') hΦ hs.le) hC
          rw [show l + 1 + k = l + (k + 1) by ring] at hrec
          calc T.hlim v - T.hlim u = (T.hlim v - T.hlim v') + (T.hlim v' - T.hlim u') +
                (T.hlim u' - T.hlim u) := by ring
            _ ≤ 0 + max (C * Φ u' v' ^ s) (T.mass (l + (k + 1))) + 0 := by gcongr
            _ ≤ max (C * Φ u v ^ s) (T.mass (l + (k + 1))) := by
                rw [zero_add, add_zero]; exact max_le_max hpow le_rfl
      · have hcount := T.card_meet_le l a huv.le
        have hk := hkey l a u v ha hu huv hv hge
        refine le_trans ?_ (le_max_left _ _)
        calc T.hlim v - T.hlim u ≤ T.mass (l + 1) * S.card := hlimit
          _ ≤ T.mass (l + 1) * ((v - u) / T.sp l + 2) :=
              mul_le_mul_of_nonneg_left hcount (T.mass_pos _).le
          _ ≤ _ := hk
  intro u v hu huv hv
  have hroot : T.Charged 0 0 := rfl
  have hX : 0 ≤ C * Φ u v ^ s := mul_nonneg hC (Real.rpow_nonneg (hΦ0 u v huv) s)
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := ((T.mass_tendsto 0).eventually (gt_mem_nhds (sub_pos.2 hlt))).exists
  have := hP k 0 0 u v hroot hu huv (by simpa using hv)
  rcases le_max_iff.1 this with h | h
  · linarith
  · have : T.hlim v - T.hlim u < T.hlim v - T.hlim u - C * Φ u v ^ s + C * Φ u v ^ s := by
      linarith
    linarith

end WindowTree

end Problems.Juggler.BeattySlope
