import Problems.Juggler.ReturnQuotients

namespace Problems.Juggler.ReturnSeams

/-- A finite chain of actual guarded transfers of ordered odd pairs. -/
structure TransferChain (m n : ℕ) (words : Fin n → List Branch) where
  lower : Fin (n + 1) → ℕ
  upper : Fin (n + 1) → ℕ
  minimum : ∀ i : Fin n, m ≤ lower i.castSucc
  ordered : ∀ i, lower i < upper i
  odd : ∀ i, lower i % 2 = 1 ∧ upper i % 2 = 1
  guarded : ∀ i : Fin n,
    follows (lower i.castSucc) (words i) ∧ follows (upper i.castSucc) (words i)
  next_lower : ∀ i : Fin n,
    ReturnWordLoss.eval (words i) (lower i.castSucc) = lower i.succ
  next_upper : ∀ i : Fin n,
    ReturnWordLoss.eval (words i) (upper i.castSucc) = upper i.succ

namespace TransferChain

def lowerNat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then T.lower ⟨i, hi⟩ else 0

def upperNat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then T.upper ⟨i, hi⟩ else 0

theorem minimum_nat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) {i : ℕ} (hi : i < n) : m ≤ T.lowerNat i := by
  simpa [lowerNat, show i < n + 1 by omega] using T.minimum ⟨i, hi⟩

theorem ordered_nat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) {i : ℕ} (hi : i < n + 1) :
    T.lowerNat i < T.upperNat i := by
  simpa [lowerNat, upperNat, hi] using T.ordered ⟨i, hi⟩

theorem odd_nat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) {i : ℕ} (hi : i < n + 1) :
    T.lowerNat i % 2 = 1 ∧ T.upperNat i % 2 = 1 := by
  simpa [lowerNat, upperNat, hi] using T.odd ⟨i, hi⟩

theorem next_nat {m n : ℕ} {words : Fin n → List Branch}
    (T : TransferChain m n words) {i : ℕ} (hi : i < n) :
    ReturnWordLoss.eval (words ⟨i, hi⟩) (T.lowerNat i) = T.lowerNat (i + 1) ∧
    ReturnWordLoss.eval (words ⟨i, hi⟩) (T.upperNat i) = T.upperNat (i + 1) := by
  simpa [lowerNat, upperNat, show i < n + 1 by omega,
    show i + 1 < n + 1 by omega] using
    And.intro (T.next_lower ⟨i, hi⟩) (T.next_upper ⟨i, hi⟩)

end TransferChain

def dcWords : Fin 2 → List Branch := fun _ => ReturnWordBounds.wordC

def lrWords (i : Fin 3) : List Branch :=
  if i.val < 2 then ReturnWordBounds.wordC else ReturnWordBounds.wordW

open ReturnWordLoss ReturnWordBounds

/-- Two actual transfers, anchored to the original OOE/OE seam. -/
theorem dc_rank_transfers {a b m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn a b y wordA wordB) (ha : 0 < a) (hb : 0 < b)
    (hm : 2 ^ 24 ≤ m) (hy : m ≤ y 0)
    (hodd : ∀ i, i < a + b → y i % 2 = 1) :
    ∃ l u : ℕ → ℕ,
      l 0 = image (y (a + b - 1)) wordB ∧ u 0 = image (y 0) wordA ∧
      (∀ i, i < 2 → m ≤ l i) ∧
      (∀ i, i < 3 → l i < u i) ∧
      (∀ i, i < 3 → l i % 2 = 1 ∧ u i % 2 = 1) ∧
      (∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
        eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1)) := by
  obtain ⟨r, s, hs, hsr, hrb, hab, hbr, HC, _⟩ := dc_rank_stages h ha hb hm hy
  let l : ℕ → ℕ := fun i => y (b - i * r - 1)
  let u : ℕ → ℕ := fun i => y (b - i * r)
  have hlo : ∀ i, i < 3 → 0 < b - i * r ∧ b - i * r < a + b := by
    intro i hi
    interval_cases i <;> norm_num <;> omega
  have hstep : ∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
      eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1) := by
    intro i hi
    have hik : r < b - i * r := by
      interval_cases i <;> norm_num <;> omega
    have hin : b - i * r < r + b := by omega
    obtain ⟨hlf, hli⟩ := HC.upper (b - i * r - 1) (by omega) (by omega)
    obtain ⟨huf, hui⟩ := HC.upper (b - i * r) (by omega) hin
    have he : b - i * r - r = b - (i + 1) * r := by simp only [Nat.add_mul, one_mul]; omega
    have he' : b - i * r - 1 - r = b - (i + 1) * r - 1 := by simp only [Nat.add_mul, one_mul]; omega
    exact ⟨hlf, huf, (eval_eq_image hlf).trans (by simpa [l, he'] using hli),
      (eval_eq_image huf).trans (by simpa [u, he] using hui)⟩
  have hseam := h.seam ha hb
  refine ⟨l, u, ?_, ?_, ?_, ?_, ?_, hstep⟩
  · simpa [l] using hseam.2.2.2.1.symm
  · simpa [u] using hseam.2.1.symm
  · intro i hi
    exact hy.trans (h.min_le (by have hh := hlo i (by omega); omega))
  · intro i hi
    have hh := hlo i hi
    exact h.ordered _ _ (by omega) hh.2
  · intro i hi
    have hh := hlo i hi
    exact ⟨hodd _ (by omega), hodd _ hh.2⟩

/-- Three actual transfers; the third uses the later upper return word. -/
theorem lr_rank_transfers {a b m : ℕ} {y : ℕ → ℕ}
    (h : RankedReturn a b y wordA wordB) (ha : 0 < a) (hb : 0 < b)
    (hm : 2 ^ 128 ≤ m) (hy : m ≤ y 0)
    (hodd : ∀ i, i < a + b → y i % 2 = 1) :
    ∃ l u : ℕ → ℕ,
      l 0 = image (y (a + b - 1)) wordB ∧ u 0 = image (y 0) wordA ∧
      (∀ i, i < 3 → m ≤ l i) ∧
      (∀ i, i < 4 → l i < u i) ∧
      (∀ i, i < 4 → l i % 2 = 1 ∧ u i % 2 = 1) ∧
      (∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
        eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1)) ∧
      follows (l 2) wordW ∧ follows (u 2) wordW ∧
      eval wordW (l 2) = l 3 ∧ eval wordW (u 2) = u 3 := by
  obtain ⟨r, s, hs, hsr, hrb, hab, hbr, HC, HD⟩ := dc_rank_stages h ha hb (by omega) hy
  obtain ⟨v, hv, hvs, hrv, HW⟩ := lr_rank_stage HD hs hsr hm hy
  let k : ℕ → ℕ := fun i => if i = 3 then s - v else b - i * r
  let l : ℕ → ℕ := fun i => y (k i - 1)
  let u : ℕ → ℕ := fun i => y (k i)
  have hlo : ∀ i, i < 4 → 0 < k i ∧ k i < a + b := by
    intro i hi
    interval_cases i <;> norm_num [k] <;> omega
  have hstep : ∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
      eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1) := by
    intro i hi
    have hk : k i = b - i * r := by simp [k, show i ≠ 3 by omega]
    have hk' : k (i + 1) = b - (i + 1) * r := by simp [k, show i + 1 ≠ 3 by omega]
    have hik : r < b - i * r := by
      interval_cases i <;> norm_num <;> omega
    have hin : b - i * r < r + b := by omega
    obtain ⟨hlf, hli⟩ := HC.upper (b - i * r - 1) (by omega) (by omega)
    obtain ⟨huf, hui⟩ := HC.upper (b - i * r) (by omega) hin
    have he : b - i * r - r = b - (i + 1) * r := by simp only [Nat.add_mul, one_mul]; omega
    have he' : b - i * r - 1 - r = b - (i + 1) * r - 1 := by simp only [Nat.add_mul, one_mul]; omega
    refine ⟨by simpa [l, hk] using hlf, by simpa [u, hk] using huf, ?_, ?_⟩
    · simpa only [l, hk, hk'] using
        (eval_eq_image hlf).trans (by simpa only [he'] using hli)
    · simpa only [u, hk, hk'] using
        (eval_eq_image huf).trans (by simpa only [he] using hui)
  have hk₂ : k 2 = s := by dsimp [k]; omega
  have hk₃ : k 3 = s - v := by simp [k]
  obtain ⟨hWl, hWu, hWli, hWui, _, _⟩ := HW.right_seam hv hvs
  have hseam := h.seam ha hb
  refine ⟨l, u, ?_, ?_, ?_, ?_, ?_, hstep, ?_, ?_, ?_, ?_⟩
  · simpa [l, k] using hseam.2.2.2.1.symm
  · simpa [u, k] using hseam.2.1.symm
  · intro i hi
    exact hy.trans (h.min_le (by have hh := hlo i (by omega); omega))
  · intro i hi
    have hh := hlo i hi
    exact h.ordered _ _ (by omega) hh.2
  · intro i hi
    have hh := hlo i hi
    exact ⟨hodd _ (by omega), hodd _ hh.2⟩
  · simpa only [l, hk₂] using hWl
  · simpa only [u, hk₂] using hWu
  · simpa only [l, hk₂, hk₃] using (eval_eq_image hWl).trans hWli
  · simpa only [u, hk₂, hk₃] using (eval_eq_image hWu).trans hWui

/-- A bounded actual periodic set supplies the complete two-transfer certificate. -/
theorem periodicExtrema_dc_transfers {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2 ^ 24 ≤ m) (hM : M < m ^ 3) :
    ∃ l u : ℕ → ℕ,
      l 0 = ReturnCells.oe M.sqrt ∧ u 0 = ReturnCells.ooe m ∧
      (∀ i, i < 2 → m ≤ l i) ∧
      (∀ i, i < 3 → l i < u i) ∧
      (∀ i, i < 3 → l i % 2 = 1 ∧ u i % 2 = 1) ∧
      (∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
        eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1)) := by
  obtain ⟨a, b, y, ha, hb, hy0, hyLast, h, hodd⟩ :=
    periodicExtrema_return_model D (by omega) hM
  change RankedReturn a b y wordA wordB at h
  have hy : m ≤ y 0 := hy0.ge
  obtain ⟨l, u, hl, hu, hmin, hlt, hod, hstep⟩ :=
    dc_rank_transfers h ha hb hm hy (fun i hi => (hodd i hi).2)
  have hs := h.seam ha hb
  refine ⟨l, u, ?_, ?_, hmin, hlt, hod, hstep⟩
  · rw [hl, wordB, image_oe_eq hs.2.2.1, hyLast]
  · rw [hu, wordA, image_ooe_eq hs.1, hy0]

/-- The later minimum scale supplies the complete three-transfer certificate. -/
theorem periodicExtrema_lr_transfers {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2 ^ 128 ≤ m) (hM : M < m ^ 3) :
    ∃ l u : ℕ → ℕ,
      l 0 = ReturnCells.oe M.sqrt ∧ u 0 = ReturnCells.ooe m ∧
      (∀ i, i < 3 → m ≤ l i) ∧
      (∀ i, i < 4 → l i < u i) ∧
      (∀ i, i < 4 → l i % 2 = 1 ∧ u i % 2 = 1) ∧
      (∀ i, i < 2 → follows (l i) wordC ∧ follows (u i) wordC ∧
        eval wordC (l i) = l (i + 1) ∧ eval wordC (u i) = u (i + 1)) ∧
      follows (l 2) wordW ∧ follows (u 2) wordW ∧
      eval wordW (l 2) = l 3 ∧ eval wordW (u 2) = u 3 := by
  obtain ⟨a, b, y, ha, hb, hy0, hyLast, h, hodd⟩ :=
    periodicExtrema_return_model D (by omega) hM
  change RankedReturn a b y wordA wordB at h
  have hy : m ≤ y 0 := hy0.ge
  obtain ⟨l, u, hl, hu, hmin, hlt, hod, hstep, hWl, hWu, hWli, hWui⟩ :=
    lr_rank_transfers h ha hb hm hy (fun i hi => (hodd i hi).2)
  have hs := h.seam ha hb
  refine ⟨l, u, ?_, ?_, hmin, hlt, hod, hstep, hWl, hWu, hWli, hWui⟩
  · rw [hl, wordB, image_oe_eq hs.2.2.1, hyLast]
  · rw [hu, wordA, image_ooe_eq hs.1, hy0]

/-- The actual DC placement packaged as a finite guarded chain. -/
theorem periodicExtrema_dc_chain {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2 ^ 24 ≤ m) (hM : M < m ^ 3) :
    ∃ T : TransferChain m 2 dcWords,
      T.lowerNat 0 = ReturnCells.oe M.sqrt ∧ T.upperNat 0 = ReturnCells.ooe m := by
  obtain ⟨l, u, hl, hu, hmin, hlt, hodd, hstep⟩ := periodicExtrema_dc_transfers D hm hM
  let T : TransferChain m 2 dcWords := {
    lower := fun i => l i.val
    upper := fun i => u i.val
    minimum := fun i => hmin i.val i.isLt
    ordered := fun i => hlt i.val i.isLt
    odd := fun i => hodd i.val i.isLt
    guarded := fun i => ⟨(hstep i.val i.isLt).1, (hstep i.val i.isLt).2.1⟩
    next_lower := fun i => (hstep i.val i.isLt).2.2.1
    next_upper := fun i => (hstep i.val i.isLt).2.2.2 }
  exact ⟨T, by simpa [T, TransferChain.lowerNat] using hl,
    by simpa [T, TransferChain.upperNat] using hu⟩

/-- The actual later placement packaged as two C steps and one W step. -/
theorem periodicExtrema_lr_chain {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2 ^ 128 ≤ m) (hM : M < m ^ 3) :
    ∃ T : TransferChain m 3 lrWords,
      T.lowerNat 0 = ReturnCells.oe M.sqrt ∧ T.upperNat 0 = ReturnCells.ooe m := by
  obtain ⟨l, u, hl, hu, hmin, hlt, hodd, hstep, hW⟩ := periodicExtrema_lr_transfers D hm hM
  have hfull (i : Fin 3) :
      follows (l i.val) (lrWords i) ∧ follows (u i.val) (lrWords i) ∧
      eval (lrWords i) (l i.val) = l (i.val + 1) ∧
      eval (lrWords i) (u i.val) = u (i.val + 1) := by
    by_cases hi : i.val < 2
    · simpa [lrWords, hi] using hstep i.val hi
    · have hi2 : i.val = 2 := by omega
      simpa [lrWords, hi2] using hW
  let T : TransferChain m 3 lrWords := {
    lower := fun i => l i.val
    upper := fun i => u i.val
    minimum := fun i => hmin i.val i.isLt
    ordered := fun i => hlt i.val i.isLt
    odd := fun i => hodd i.val i.isLt
    guarded := fun i => ⟨(hfull i).1, (hfull i).2.1⟩
    next_lower := fun i => (hfull i).2.2.1
    next_upper := fun i => (hfull i).2.2.2 }
  exact ⟨T, by simpa [T, TransferChain.lowerNat] using hl,
    by simpa [T, TransferChain.upperNat] using hu⟩

/-- At a two-rank terminal return the word invariant describes both actual paths. -/
theorem RankedReturn.terminal_actual_factorization {U V : List Branch} {y : ℕ → ℕ}
    (h : RankedReturn 1 1 y U V) (hwords : ReturnWordFactorization.InducedPair U V) :
    y 0 < y 1 ∧ ∃ P Q, ReturnWordFactorization.Factorization U V P Q ∧
      follows (y 0) P ∧ follows (y 1) P ∧
      (image (y 0) P) % 2 = 1 ∧ (floorPower (image (y 0) P)) % 2 = 0 ∧
      (image (y 1) P) % 2 = 0 ∧ (floorPower (image (y 1) P)) % 2 = 1 ∧
      follows (floorPower (floorPower (image (y 0) P))) Q ∧
      follows (floorPower (floorPower (image (y 1) P))) Q ∧
      image (floorPower (floorPower (image (y 0) P))) Q = y 0 ∧
      image (floorPower (floorPower (image (y 1) P))) Q = y 1 := by
  have hU := h.lower 0 (by decide)
  have hV := h.upper 1 (by decide) (by decide)
  exact ⟨h.ordered 0 1 (by decide) (by decide),
    ReturnWordFactorization.induced_terminal_actual_factorization
      hwords hU.1 hV.1 hU.2 hV.2⟩

end Problems.Juggler.ReturnSeams
