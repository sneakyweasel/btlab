import Problems.Juggler.ReturnInduction
import Problems.Juggler.CubicReturn
import Problems.Juggler.ReturnWordFactorization

namespace Problems.Juggler.ReturnSeams

/-- Guarded words realize the two rank branches on one ordered list of values. -/
structure RankedReturn (a b : ℕ) (y : ℕ → ℕ) (U V : List Branch) : Prop where
  ordered : ∀ i j, i < j → j < a + b → y i < y j
  lower : ∀ i, i < a → follows (y i) U ∧ image (y i) U = y (i + b)
  upper : ∀ i, a ≤ i → i < a + b →
    follows (y i) V ∧ image (y i) V = y (i - a)

namespace RankedReturn

variable {a b : ℕ} {y : ℕ → ℕ} {U V : List Branch}
variable (h : RankedReturn a b y U V)
include h

theorem min_le {i : ℕ} (hi : i < a + b) : y 0 ≤ y i := by
  by_cases hi0 : i = 0
  · simp [hi0]
  · exact (h.ordered 0 i (by omega) hi).le

/-- Left induction preserves both the actual guards and the return values. -/
theorem left (hba : b ≤ a) : RankedReturn (a - b) b y U (U ++ V) := by
  constructor
  · intro i j hij hj
    exact h.ordered i j hij (by omega)
  · intro i hi
    exact h.lower i (by omega)
  · intro i hi hin
    obtain ⟨hU, hUi⟩ := h.lower i (by omega)
    obtain ⟨hV, hVi⟩ := h.upper (i + b) (by omega) (by omega)
    refine ⟨follows_append hU (by simpa [hUi] using hV), ?_⟩
    rw [image_append, hUi, hVi]
    congr 1
    omega

/-- Right induction has the same guard-preserving interpretation. -/
theorem right (hab : a ≤ b) : RankedReturn a (b - a) y (U ++ V) V := by
  constructor
  · intro i j hij hj
    exact h.ordered i j hij (by omega)
  · intro i hi
    obtain ⟨hU, hUi⟩ := h.lower i hi
    obtain ⟨hV, hVi⟩ := h.upper (i + b) (by omega) (by omega)
    refine ⟨follows_append hU (by simpa [hUi] using hV), ?_⟩
    rw [image_append, hUi, hVi]
    congr 1
    omega
  · intro i hi hin
    exact h.upper i hi (by omega)

theorem seam (ha : 0 < a) (hb : 0 < b) :
    follows (y 0) U ∧ image (y 0) U = y b ∧
      follows (y (a + b - 1)) V ∧ image (y (a + b - 1)) V = y (b - 1) ∧
      y (b - 1) < y b := by
  obtain ⟨hU, hUi⟩ := h.lower 0 ha
  obtain ⟨hV, hVi⟩ := h.upper (a + b - 1) (by omega) (by omega)
  have he : a + b - 1 - a = b - 1 := by omega
  simpa only [zero_add, he] using
    And.intro hU (And.intro hUi (And.intro hV
      (And.intro hVi (h.ordered (b - 1) b (by omega) (by omega)))))

theorem odd_seam_gap (ha : 0 < a) (hb : 0 < b)
    (hodd : ∀ i, i < a + b → y i % 2 = 1) :
    y (b - 1) + 2 ≤ y b := by
  have hs := (h.seam ha hb).2.2.2.2
  have hw := hodd (b - 1) (by omega)
  have hz := hodd b (by omega)
  omega

/-- A left step reuses exactly the same two seam values. -/
theorem left_seam (hb : 0 < b) (hba : b < a) :
    image (y (a - 1)) U = y (a + b - 1) ∧
      image (y (a - 1)) (U ++ V) = y (b - 1) ∧
      image (y 0) U = y b := by
  have h₁ := (h.lower (a - 1) (by omega)).2
  have h₂ := ((h.left hba.le).upper (a - 1) (by omega) (by omega)).2
  have h₃ := (h.lower 0 (by omega)).2
  have he₁ : a - 1 + b = a + b - 1 := by omega
  have he₂ : a - 1 - (a - b) = b - 1 := by omega
  simpa only [he₁, he₂, zero_add] using And.intro h₁ (And.intro h₂ h₃)

/-- A right step transports two guarded adjacent seam sources by the upper word. -/
theorem right_seam (ha : 0 < a) (hab : a < b) :
    follows (y (b - 1)) V ∧ follows (y b) V ∧
      image (y (b - 1)) V = y (b - a - 1) ∧
      image (y b) V = y (b - a) ∧
      y (b - a - 1) < y (b - a) ∧
      y (b - a) ≤ y (b - 1) := by
  obtain ⟨hw, hwi⟩ := h.upper (b - 1) (by omega) (by omega)
  obtain ⟨hz, hzi⟩ := h.upper b (by omega) (by omega)
  have he : b - 1 - a = b - a - 1 := by omega
  refine ⟨hw, hz, by simpa only [he] using hwi, hzi,
    h.ordered _ _ (by omega) (by omega), ?_⟩
  by_cases heq : b - a = b - 1
  · simp [heq]
  · exact (h.ordered _ _ (by omega) (by omega)).le

/-- At equality the concatenated return fixes the retained prefix. -/
theorem equality_fixes (hab : a = b) {i : ℕ} (hi : i < a) :
    follows (y i) (U ++ V) ∧ image (y i) (U ++ V) = y i := by
  have hn := (h.left (by omega)).upper i (by omega) (by omega)
  simpa [hab] using hn

/-- The final restriction keeps the lower seam point and removes the upper one. -/
theorem equality_removes_upper (hab : a = b) (hb : 0 < b) :
    (∃ i < b, y i = y (b - 1)) ∧ ¬ ∃ i < b, y i = y b := by
  refine ⟨⟨b - 1, by omega, rfl⟩, ?_⟩
  rintro ⟨i, hi, he⟩
  have hlt := h.ordered i b hi (by omega)
  omega

/-- Growth of the concatenated word forbids a left or equal next step. -/
theorem lt_of_concat_grows {m : ℕ} (hm : m ≤ y 0) (hb : 0 < b)
    (hg : ∀ x, m ≤ x → follows x (U ++ V) → x < image x (U ++ V)) : a < b := by
  by_contra hn
  have hba : b ≤ a := by omega
  have hnew := h.left hba
  obtain ⟨hf, he⟩ := hnew.upper (a - b) (by omega) (by omega)
  have hmin := h.min_le (show a - b < a + b by omega)
  have hx := hg (y (a - b)) (hm.trans hmin) hf
  simp only [Nat.sub_self] at he
  omega

/-- Decrease of the concatenated word forbids a right or equal next step. -/
theorem lt_of_concat_decreases {m : ℕ} (hm : m ≤ y 0) (ha : 0 < a)
    (hd : ∀ x, m ≤ x → follows x (U ++ V) → image x (U ++ V) < x) : b < a := by
  by_contra hn
  have hab : a ≤ b := by omega
  obtain ⟨hf, he⟩ := (h.right hab).lower 0 ha
  have hx := hd (y 0) hm hf
  have hmin := h.min_le (show b - a < a + b by omega)
  simp only [zero_add] at he
  omega

end RankedReturn

end Problems.Juggler.ReturnSeams
