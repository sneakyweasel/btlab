import Problems.Juggler.BeattySlopeRationalLimit

/-!
# The weak positive-partial-sum recurrence at every boundary

At a rational boundary the survival convention `β*k ≤ odd` is weak, so the
terminal binomial sum in the renewal recurrence must also be weak. For a
fixed depth, every irrational boundary slightly below `β` has the same
survivor words up to that depth, and its strict terminal sums equal the weak
terminal sums at `β`. The irrational recurrence therefore transfers exactly.
No power-series argument is repeated.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- Weighted weak endpoint binomial sum: odd counts `k` with `n*β ≤ k`.
At an irrational boundary and positive depth it equals `endpointWeight`. -/
noncomputable def weakEndpointWeight (β z : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n+1), if (n : ℝ)*β ≤ k then (n.choose k : ℝ)*z^k else 0

/-- Nonnegative letter weights give nonnegative weak endpoint sums. -/
theorem weakEndpointWeight_nonneg (β : ℝ) {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ weakEndpointWeight β z n := by
  apply sum_nonneg
  intro k _
  split_ifs <;> positivity

private theorem strict_eventually_left (β₀ : ℝ) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∀ᶠ β : ℝ in 𝓝[<] β₀, ((m : ℝ)*β < k ↔ (m : ℝ)*β₀ ≤ k) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases h : (m : ℝ)*β₀ ≤ k
  · filter_upwards [self_mem_nhdsWithin] with β hb
    have hb' : β < β₀ := hb
    exact ⟨fun _ => h, fun _ => by nlinarith⟩
  · have hgt : (k : ℝ) < m*β₀ := lt_of_not_ge h
    have ht : Tendsto (fun β : ℝ => (m : ℝ)*β) (𝓝 β₀) (𝓝 ((m : ℝ)*β₀)) :=
      (continuous_const.mul continuous_id).tendsto β₀
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ht (Ioi_mem_nhds hgt))]
      with β hb
    exact ⟨fun h' => absurd h' (not_lt.2 (Set.mem_Ioi.1 hb).le), fun h' => absurd h' h⟩

private theorem endpoint_eventually_left (β₀ z : ℝ) {m : ℕ} (hm : 0 < m) :
    ∀ᶠ β in 𝓝[<] β₀, endpointWeight β z m = weakEndpointWeight β₀ z m := by
  have h : ∀ᶠ β in 𝓝[<] β₀, ∀ k ∈ range (m+1), ((m : ℝ)*β < k ↔ (m : ℝ)*β₀ ≤ k) :=
    (eventually_all_finset _).2 fun k _ => strict_eventually_left β₀ hm k
  filter_upwards [h] with β hβ
  unfold endpointWeight weakEndpointWeight
  exact sum_congr rfl fun k hk => by simp only [hβ k hk]

private theorem survives_eventually_left (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[<] β₀, ∀ w ∈ allWords n, (Survives β w ↔ Survives β₀ w) := by
  have h : ∀ᶠ β : ℝ in 𝓝[<] β₀, ∀ k ∈ range (n+1), ∀ m ∈ range (n+1),
      0 < k → (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) := by
    rw [eventually_all_finset]
    intro k _
    rw [eventually_all_finset]
    intro m _
    by_cases hk : 0 < k
    · filter_upwards [cmp_eventually_left β₀ hk m] with β h _
      exact h
    · exact Eventually.of_forall fun _ h => absurd h hk
  filter_upwards [h] with β h w hw
  have hlen : w.length = n := mem_allWords.mp hw
  unfold Survives
  refine forall_congr' fun k => imp_congr_right fun hkl => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hm : oddCount (w.take k) ≤ n :=
      (oddCount_le_length _).trans ((List.length_take_le _ _).trans (by omega))
    exact h k (mem_range.2 (by omega)) _ (mem_range.2 (by omega)) hk

private theorem survivorWeight_eventually_left (β₀ z : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[<] β₀, survivorWeight β z n = survivorWeight β₀ z n := by
  filter_upwards [survives_eventually_left β₀ n] with β h
  unfold survivorWeight survivorWords
  congr 1
  ext w
  simp only [mem_filter]
  exact ⟨fun hw => ⟨hw.1, (h w hw.1).1 hw.2⟩, fun hw => ⟨hw.1, (h w hw.1).2 hw.2⟩⟩

/-- The exact weighted renewal recurrence at every real boundary, rational
ones included, with the weak terminal binomial sums. At an irrational
boundary it is `survivorWeight_recurrence`. -/
theorem survivorWeight_weak_recurrence (β z : ℝ) (n : ℕ) :
    (n : ℝ)*survivorWeight β z n =
      ∑ j ∈ range n, weakEndpointWeight β z (n-j)*survivorWeight β z j := by
  have hS : ∀ᶠ β' in 𝓝[<] β, ∀ m ∈ range (n+1),
      survivorWeight β' z m = survivorWeight β z m :=
    (eventually_all_finset _).2 fun m _ => survivorWeight_eventually_left β z m
  have hE : ∀ᶠ β' in 𝓝[<] β, ∀ m ∈ range (n+1), 0 < m →
      endpointWeight β' z m = weakEndpointWeight β z m :=
    (eventually_all_finset _).2 fun m _ => by
      by_cases hm : 0 < m
      · filter_upwards [endpoint_eventually_left β z hm] with β' h _
        exact h
      · exact Eventually.of_forall fun _ h => absurd h hm
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hS.and hE)
  obtain ⟨β', hirr, h1, h2⟩ := exists_irrational_btwn (show l < β from hl)
  obtain ⟨hS', hE'⟩ := hsub ⟨h1, h2⟩
  have hrec := survivorWeight_recurrence β' hirr z n
  rw [hS' n (mem_range.2 (by omega))] at hrec
  rw [hrec]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.1 hj
  rw [hS' j (mem_range.2 (by omega)), hE' (n-j) (mem_range.2 (by omega)) (by omega)]

end Problems.Juggler.BeattySlope
