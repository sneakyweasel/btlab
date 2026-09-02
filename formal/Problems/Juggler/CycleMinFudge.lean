import Problems.Juggler.O7EEEEGap
import Problems.Juggler.EvenCountThree

namespace Problems.Juggler

/-!
# CycleMin (n+1)/n fudge

Laboratory satellite. On a `CycleMin` every later state is `≥ n`, so
`(x+1)/x ≤ (n+1)/n`. The even sibling of `absorb_odd_step` plus that
crossing keeps slack `3^7 - 2^11 = 139` on every 7-odd itinerary that
starts `O`. On any start-`O` four-even itinerary with `o ≥ 7` odds the
slack is `3^o - 2^{o+4}`. The thirty first-expanding short-gap
leftovers are not `CycleMin` words. The eight leftovers whose only
CycleMin-shaped rotation is themselves are not cycle itineraries.

Not imported by `Problems.JugglerPaper`. Not a length-11 census, not
`no_cycle_itinerary_four_even`, and not a halt theorem.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 20000

/-! ## Exponent machine -/

@[ext]
structure ChainExponents where
  A : ℕ
  B : ℕ
  gamma : ℕ
  deriving DecidableEq, Repr

def absorbOddExponents (s : ChainExponents) : ChainExponents :=
  if s.gamma = 0 then
    ⟨3, 0, 2⟩
  else
    let A := if s.gamma % 3 = 0 then s.A else 3 * s.A
    let B := if s.gamma % 3 = 0 then s.B else 3 * s.B
    let γ := if s.gamma % 3 = 0 then s.gamma else 3 * s.gamma
    let t := γ / 3
    ⟨A + 3 * t, B + 3 * t, 2 * t⟩

def absorbEvenExponents (s : ChainExponents) : ChainExponents :=
  if s.gamma = 0 then
    ⟨1, 0, 2⟩
  else
    ⟨s.A + s.gamma, s.B + s.gamma, 2 * s.gamma⟩

def exponentsAfter (w : List Branch) : ChainExponents :=
  w.foldl (fun s b =>
    match b with
    | .odd => absorbOddExponents s
    | .even => absorbEvenExponents s) ⟨0, 0, 0⟩

def trailingEvenCount (w : List Branch) : ℕ :=
  (w.reverse.takeWhile (fun b => b == .even)).length

def dropTrailingEvens (w : List Branch) : List Branch :=
  (w.reverse.dropWhile (fun b => b == .even)).reverse

def fourEvenWord (a0 a1 a2 a3 : ℕ) : List Branch :=
  List.replicate a0 .odd ++ [.even] ++
    List.replicate a1 .odd ++ [.even] ++
      List.replicate a2 .odd ++ [.even] ++
        List.replicate a3 .odd ++ [.even]

structure FourEvenParams where
  a0 : ℕ
  a1 : ℕ
  a2 : ℕ
  a3 : ℕ
  deriving DecidableEq, Repr

def fudgeParams : List FourEvenParams :=
  [⟨7, 0, 0, 0⟩, ⟨6, 1, 0, 0⟩, ⟨5, 2, 0, 0⟩, ⟨4, 3, 0, 0⟩, ⟨3, 4, 0, 0⟩,
    ⟨2, 5, 0, 0⟩, ⟨6, 0, 0, 1⟩, ⟨5, 1, 0, 1⟩, ⟨4, 2, 0, 1⟩, ⟨3, 3, 0, 1⟩,
    ⟨2, 4, 0, 1⟩, ⟨6, 0, 1, 0⟩, ⟨5, 1, 1, 0⟩, ⟨4, 2, 1, 0⟩, ⟨3, 3, 1, 0⟩,
    ⟨2, 4, 1, 0⟩, ⟨5, 0, 1, 1⟩, ⟨4, 1, 1, 1⟩, ⟨3, 2, 1, 1⟩, ⟨2, 3, 1, 1⟩,
    ⟨5, 0, 2, 0⟩, ⟨4, 1, 2, 0⟩, ⟨3, 2, 2, 0⟩, ⟨2, 3, 2, 0⟩, ⟨4, 0, 2, 1⟩,
    ⟨3, 1, 2, 1⟩, ⟨2, 2, 2, 1⟩, ⟨4, 0, 3, 0⟩, ⟨3, 1, 3, 0⟩, ⟨2, 2, 3, 0⟩]

def fudgeWords : List (List Branch) :=
  fudgeParams.map fun p => fourEvenWord p.a0 p.a1 p.a2 p.a3

def noFollowsFrom2Below (w : List Branch) (N : ℕ) : Bool :=
  (List.range N).all fun n => decide (n < 2) || !followsB n w

def startsTwoOddsEndsEven (w : List Branch) : Bool :=
  decide (w.head? == some Branch.odd) &&
    decide (w[1]?.getD Branch.even == Branch.odd) &&
    decide (w.getLast? == some Branch.even)

def onlySelfCycleMinShape (w : List Branch) : Bool :=
  (List.range w.length).all fun k =>
    !startsTwoOddsEndsEven (rotateItinerary w k) || decide (rotateItinerary w k == w)

def fudgeReady (w : List Branch) : Bool :=
  decide (w.head? == some Branch.odd) &&
    decide (w.getLast? == some Branch.even) &&
    decide (oddCount w == 7) &&
    decide (w.length == 11) &&
    decide ((exponentsAfter (dropTrailingEvens w)).A ≤ 13905) &&
    decide (1 ≤ trailingEvenCount w) &&
    noFollowsFrom2Below (dropTrailingEvens w) 30 &&
    decide (dropTrailingEvens w ≠ [])

/-! ## Even sibling and scaling -/

theorem even_succ_sq_gt {x : ℕ} (he : x % 2 = 0) :
    x < (floorPower x + 1) ^ 2 :=
  ((floorPower_even_eq_iff_sq_interval he).mp rfl).2

theorem raise_chain {n x A B γ k : ℕ} (hk : k ≠ 0)
    (h : n ^ A < (n + 1) ^ B * (x + 1) ^ γ) :
    n ^ (k * A) < (n + 1) ^ (k * B) * (x + 1) ^ (k * γ) := by
  have hpow :
      (n ^ A) ^ k < ((n + 1) ^ B * (x + 1) ^ γ) ^ k :=
    Nat.pow_lt_pow_left h hk
  have hL : (n ^ A) ^ k = n ^ (A * k) := (Nat.pow_mul n A k).symm
  have hR : ((n + 1) ^ B * (x + 1) ^ γ) ^ k =
      (n + 1) ^ (B * k) * (x + 1) ^ (γ * k) := by
    rw [mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
  have hL' : n ^ (A * k) = n ^ (k * A) := by rw [Nat.mul_comm]
  have hR' : (n + 1) ^ (B * k) * (x + 1) ^ (γ * k) =
      (n + 1) ^ (k * B) * (x + 1) ^ (k * γ) := by
    rw [Nat.mul_comm B, Nat.mul_comm γ]
  exact (hL' ▸ (hL ▸ hpow)).trans_eq (hR.trans hR')

/-- One CycleMin-crossing even step: `x < (T(x)+1)^2` and
`(x+1)/x ≤ (n+1)/n`. -/
theorem absorb_even_step {n x A B γ : ℕ} (hn : 1 ≤ n)
    (h : n ^ A < (n + 1) ^ B * (x + 1) ^ γ)
    (hx : n ≤ x) (heven : x % 2 = 0) (hγ : γ ≠ 0) :
    n ^ (A + γ) <
      (n + 1) ^ (B + γ) * (floorPower x + 1) ^ (2 * γ) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hn
  have hL : n ^ (A + γ) = n ^ A * n ^ γ := Nat.pow_add _ _ _
  have hmul : n ^ A * n ^ γ <
      (n + 1) ^ B * (x + 1) ^ γ * n ^ γ :=
    Nat.mul_lt_mul_of_pos_right h (pow_pos hn0 _)
  have hcross := cross_mul_pow (n := n) (x := x) (e := γ) hx
  have hmid :
      (n + 1) ^ B * ((x + 1) ^ γ * n ^ γ) ≤
        (n + 1) ^ B * ((n + 1) ^ γ * x ^ γ) :=
    Nat.mul_le_mul_left _ hcross
  have hassoc :
      (n + 1) ^ B * (x + 1) ^ γ * n ^ γ =
        (n + 1) ^ B * ((x + 1) ^ γ * n ^ γ) :=
    mul_assoc _ _ _
  have hassoc' :
      (n + 1) ^ B * ((n + 1) ^ γ * x ^ γ) =
        (n + 1) ^ (B + γ) * x ^ γ := by
    rw [← mul_assoc, ← Nat.pow_add]
  have hle :
      (n + 1) ^ B * (x + 1) ^ γ * n ^ γ ≤
        (n + 1) ^ (B + γ) * x ^ γ :=
    (hassoc ▸ hmid).trans_eq hassoc'
  have hcell : x < (floorPower x + 1) ^ 2 := even_succ_sq_gt heven
  have hxt : x ^ γ < ((floorPower x + 1) ^ 2) ^ γ :=
    Nat.pow_lt_pow_left hcell hγ
  have h2t : ((floorPower x + 1) ^ 2) ^ γ = (floorPower x + 1) ^ (2 * γ) :=
    (Nat.pow_mul (floorPower x + 1) 2 γ).symm
  have hxlt : x ^ γ < (floorPower x + 1) ^ (2 * γ) := by
    rwa [← h2t]
  have hposB : 0 < (n + 1) ^ (B + γ) := pow_pos (Nat.succ_pos n) _
  have hfin :
      (n + 1) ^ (B + γ) * x ^ γ <
        (n + 1) ^ (B + γ) * (floorPower x + 1) ^ (2 * γ) :=
    Nat.mul_lt_mul_of_pos_left hxlt hposB
  exact ((hL ▸ hmul).trans_le hle).trans hfin

/-! ## Combinatorial lemmas -/

theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
      rw [hpow, Nat.mul_mod]
      rcases ih with h | h <;> simp [h]

theorem two_pow_not_mod_three (k : ℕ) : 2 ^ k % 3 ≠ 0 := by
  rcases two_pow_mod_three k with h | h <;> omega

theorem two_pow_pos (k : ℕ) : 0 < 2 ^ k :=
  pow_pos (by decide : (0 : ℕ) < 2) k

theorem two_pow_ne_zero (k : ℕ) : 2 ^ k ≠ 0 :=
  (two_pow_pos k).ne'

theorem absorbOdd_of_two_pow (A B k : ℕ) :
    absorbOddExponents ⟨A, B, 2 ^ k⟩ =
      ⟨3 * A + 3 * 2 ^ k, 3 * B + 3 * 2 ^ k, 2 * 2 ^ k⟩ := by
  have h0 : 2 ^ k ≠ 0 := two_pow_ne_zero k
  have h3 : 2 ^ k % 3 ≠ 0 := two_pow_not_mod_three k
  have hdiv : 3 * 2 ^ k / 3 = 2 ^ k := Nat.mul_div_right (2 ^ k) (by decide : 0 < 3)
  simp [absorbOddExponents, h3, hdiv]

theorem absorbEven_of_pos (A B γ : ℕ) (hγ : γ ≠ 0) :
    absorbEvenExponents ⟨A, B, γ⟩ = ⟨A + γ, B + γ, 2 * γ⟩ := by
  simp [absorbEvenExponents, hγ]

theorem absorbEven_struct (s : ChainExponents) (hγ : s.gamma ≠ 0) :
    absorbEvenExponents s = ⟨s.A + s.gamma, s.B + s.gamma, 2 * s.gamma⟩ := by
  simp [absorbEvenExponents, hγ]

theorem absorbOdd_struct (s : ChainExponents) (hγ : s.gamma ≠ 0)
    (h3 : s.gamma % 3 ≠ 0) :
    absorbOddExponents s =
      ⟨3 * s.A + 3 * s.gamma, 3 * s.B + 3 * s.gamma, 2 * s.gamma⟩ := by
  have hdiv : 3 * s.gamma / 3 = s.gamma :=
    Nat.mul_div_right s.gamma (by decide : (0 : ℕ) < 3)
  simp [absorbOddExponents, hγ, h3, hdiv]

theorem exponentsAfter_concat (u : List Branch) (b : Branch) :
    exponentsAfter (u ++ [b]) =
      match b with
      | .odd => absorbOddExponents (exponentsAfter u)
      | .even => absorbEvenExponents (exponentsAfter u) := by
  simp [exponentsAfter, List.foldl_append]

theorem exponentsAfter_odd_nil :
    exponentsAfter [.odd] = ⟨3, 0, 2⟩ := by
  simp [exponentsAfter, absorbOddExponents]

theorem exponents_starts_odd :
    ∀ w : List Branch, w.head? = some .odd →
      (exponentsAfter w).gamma = 2 ^ w.length ∧
        (exponentsAfter w).A =
          (exponentsAfter w).B + 3 ^ oddCount w := by
  intro w
  refine List.reverseRecOn w ?nil ?snoc
  · intro h
    simp at h
  · intro u b ih h
    cases u with
    | nil =>
        have hb : b = .odd := by
          simpa [List.head?] using h
        subst hb
        simp [exponentsAfter_odd_nil, oddCount]
    | cons x xs =>
        have hu : (x :: xs).head? = some Branch.odd := by
          simpa [List.head?, List.cons_append] using h
        have ⟨hγ, hA⟩ := ih hu
        have hγ0 : (exponentsAfter (x :: xs)).gamma ≠ 0 := by
          rw [hγ]
          exact two_pow_ne_zero _
        cases b with
        | even =>
            rw [exponentsAfter_concat (x :: xs) Branch.even,
              absorbEven_struct _ hγ0]
            constructor
            · calc
                2 * (exponentsAfter (x :: xs)).gamma
                  = 2 * 2 ^ (x :: xs).length := by rw [hγ]
                _ = 2 ^ ((x :: xs).length + 1) := by rw [Nat.mul_comm, pow_succ]
                _ = 2 ^ (x :: xs ++ [Branch.even]).length := by simp
            · have hoddEq :
                  oddCount (x :: xs ++ [.even]) = oddCount (x :: xs) := by
                rw [oddCount_append]
                simp [oddCount]
              change (exponentsAfter (x :: xs)).A + (exponentsAfter (x :: xs)).gamma =
                (exponentsAfter (x :: xs)).B + (exponentsAfter (x :: xs)).gamma +
                  3 ^ oddCount (x :: xs ++ [.even])
              rw [hA, hoddEq]
              ac_rfl
        | odd =>
            have h3 : (exponentsAfter (x :: xs)).gamma % 3 ≠ 0 := by
              rw [hγ]
              exact two_pow_not_mod_three _
            rw [exponentsAfter_concat (x :: xs) Branch.odd,
              absorbOdd_struct _ hγ0 h3]
            constructor
            · calc
                2 * (exponentsAfter (x :: xs)).gamma
                  = 2 * 2 ^ (x :: xs).length := by rw [hγ]
                _ = 2 ^ ((x :: xs).length + 1) := by rw [Nat.mul_comm, pow_succ]
                _ = 2 ^ (x :: xs ++ [Branch.odd]).length := by simp
            · have hoddEq :
                  oddCount (x :: xs ++ [.odd]) = oddCount (x :: xs) + 1 := by
                rw [oddCount_append]
                simp [oddCount]
              change 3 * (exponentsAfter (x :: xs)).A +
                  3 * (exponentsAfter (x :: xs)).gamma =
                3 * (exponentsAfter (x :: xs)).B +
                    3 * (exponentsAfter (x :: xs)).gamma +
                  3 ^ oddCount (x :: xs ++ [.odd])
              rw [hA, hoddEq, pow_succ]
              ring

theorem family_slack139 : (3 : ℕ) ^ 7 - 2 ^ 11 = 139 := by decide

/-- Slack of a start-`O` four-even itinerary with `o` odds: `3^o - 2^{o+4}`. -/
def familySlack (o : ℕ) : ℕ := 3 ^ o - 2 ^ (o + 4)

theorem familySlack_seven : familySlack 7 = 139 := family_slack139

theorem familySlack_eight : familySlack 8 = 2465 := by decide

theorem two_pow_add_four_le_three_pow {o : ℕ} (ho : 7 ≤ o) :
    2 ^ (o + 4) ≤ 3 ^ o := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ho
  clear ho
  induction k with
  | zero =>
      decide
  | succ k ih =>
      have h2 : 2 ^ (7 + (k + 1) + 4) = 2 * 2 ^ (7 + k + 4) := by
        rw [show 7 + (k + 1) + 4 = 7 + k + 4 + 1 by omega, pow_succ,
          Nat.mul_comm]
      have h3 : 3 ^ (7 + (k + 1)) = 3 * 3 ^ (7 + k) := by
        rw [show 7 + (k + 1) = 7 + k + 1 by omega, pow_succ, Nat.mul_comm]
      rw [h2, h3]
      exact (Nat.mul_le_mul_left 2 ih).trans
        (Nat.mul_le_mul_right _ (by decide : (2 : ℕ) ≤ 3))

theorem familySlack_add {o : ℕ} (ho : 7 ≤ o) :
    familySlack o + 2 ^ (o + 4) = 3 ^ o :=
  Nat.sub_add_cancel (two_pow_add_four_le_three_pow ho)

/-- On any start-`O` itinerary the leftover of `A` versus the trailing-even
cell is `3^{#O} - 2^{|pref|+r}`. -/
theorem exponents_slack_add {pref : List Branch} {r : ℕ}
    (h0 : pref.head? = some .odd) :
    (exponentsAfter pref).A + 2 ^ (pref.length + r) =
      (exponentsAfter pref).B + (exponentsAfter pref).gamma * 2 ^ r +
        3 ^ oddCount pref := by
  obtain ⟨hγ, hA⟩ := exponents_starts_odd pref h0
  rw [hA, hγ, Nat.pow_add]
  ac_rfl

theorem exponents_slack {pref : List Branch} {r : ℕ}
    (h0 : pref.head? = some .odd)
    (hge : 2 ^ (pref.length + r) ≤ 3 ^ oddCount pref) :
    (exponentsAfter pref).A =
      (exponentsAfter pref).B + (exponentsAfter pref).gamma * 2 ^ r +
        (3 ^ oddCount pref - 2 ^ (pref.length + r)) := by
  have hadd := exponents_slack_add (pref := pref) (r := r) h0
  rw [← Nat.add_sub_assoc hge, ← hadd, Nat.add_sub_cancel]

theorem slack_of_four_even {pref : List Branch} {r o : ℕ}
    (h0 : pref.head? = some .odd) (hodd : oddCount pref = o)
    (hlen : pref.length + r = o + 4) (ho : 7 ≤ o) :
    (exponentsAfter pref).A =
      (exponentsAfter pref).B + (exponentsAfter pref).gamma * 2 ^ r +
        familySlack o := by
  have hge : 2 ^ (pref.length + r) ≤ 3 ^ oddCount pref := by
    rw [hlen, hodd]
    exact two_pow_add_four_le_three_pow ho
  simpa [hodd, hlen, familySlack] using exponents_slack h0 hge

theorem dropTrailing_snoc_even (u : List Branch) :
    dropTrailingEvens (u ++ [.even]) = dropTrailingEvens u := by
  simp [dropTrailingEvens, List.reverse_append]

theorem trailing_snoc_even (u : List Branch) :
    trailingEvenCount (u ++ [.even]) = trailingEvenCount u + 1 := by
  simp [trailingEvenCount, List.reverse_append]

theorem dropTrailing_snoc_odd (u : List Branch) :
    dropTrailingEvens (u ++ [.odd]) = u ++ [.odd] := by
  simp [dropTrailingEvens, List.reverse_append]

theorem trailing_snoc_odd (u : List Branch) :
    trailingEvenCount (u ++ [.odd]) = 0 := by
  simp [trailingEvenCount, List.reverse_append]

theorem replicate_succ_snoc (n : ℕ) (a : Branch) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  simpa using List.replicate_add n 1 (a := a)

theorem split_trailing_evens :
    ∀ w : List Branch,
      w = dropTrailingEvens w ++
        List.replicate (trailingEvenCount w) Branch.even := by
  intro w
  refine List.reverseRecOn w ?nil ?snoc
  · simp [dropTrailingEvens, trailingEvenCount]
  · intro u b ih
    cases b with
    | even =>
        rw [dropTrailing_snoc_even, trailing_snoc_even, replicate_succ_snoc,
          ← List.append_assoc, ← ih]
    | odd =>
        rw [dropTrailing_snoc_odd, trailing_snoc_odd]
        simp

theorem trailingEvenCount_of_last_even {w : List Branch}
    (h : w.getLast? = some .even) : 1 ≤ trailingEvenCount w := by
  obtain ⟨u, rfl⟩ := (List.getLast?_eq_some_iff).mp h
  rw [trailing_snoc_even]
  exact Nat.succ_pos _

theorem not_follows_zero_of_odd_head {w : List Branch}
    (h : w.head? = some .odd) : ¬follows 0 w := by
  match w with
  | [] => simp at h
  | .even :: _ => simp [List.head?] at h
  | .odd :: _ =>
      intro hf
      exact absurd hf.1 (by decide)

theorem not_follows_one_of_even {w : List Branch}
    (h : 1 ≤ evenCount w) : ¬follows 1 w := by
  induction w with
  | nil => simp [evenCount] at h
  | cons b rest ih =>
      cases b with
      | even =>
          intro hf
          exact absurd hf.1 (by decide)
      | odd =>
          have hrest : 1 ≤ evenCount rest := by simpa [evenCount] using h
          intro hf
          have hf' : follows (floorPower 1) rest := hf.2
          rw [floorPower_one] at hf'
          exact ih hrest hf'

/-! ## Prefix +1-chain on a CycleMin -/

theorem take_succ_append {w : List Branch} {k : ℕ}
    (hk : k < w.length) :
    w.take (k + 1) = w.take k ++ [w[k]] :=
  List.take_succ_eq_append_getElem (l := w) (i := k) hk

theorem exponentsAfter_take_succ {w : List Branch} {k : ℕ}
    (hk : k < w.length) :
    exponentsAfter (w.take (k + 1)) =
      match w[k] with
      | .odd => absorbOddExponents (exponentsAfter (w.take k))
      | .even => absorbEvenExponents (exponentsAfter (w.take k)) := by
  rw [take_succ_append hk, exponentsAfter_concat]

theorem plus_one_chain_take {n : ℕ} {w : List Branch}
    (hn : 1 ≤ n) (h0 : w.head? = some .odd)
    (hw : follows n w)
    (hmin : ∀ j, j < w.length → n ≤ floorPower^[j] n) :
    ∀ k, 0 < k → k ≤ w.length →
      let s := exponentsAfter (w.take k)
      n ^ s.A < (n + 1) ^ s.B * (image n (w.take k) + 1) ^ s.gamma := by
  intro k hk0 hk
  induction k with
  | zero => exact (Nat.not_lt_zero 0 hk0).elim
  | succ k ih =>
      have hwne : w ≠ [] := by
        intro he
        subst he
        simp at h0
      cases k with
      | zero =>
          have htake : w.take 1 = [w.head hwne] := by
            cases w with
            | nil => exact (hwne rfl).elim
            | cons b rest => simp [List.head]
          have hb : w.head hwne = .odd := by
            simpa [List.head?_eq_some_head hwne] using h0
          have hodd : n % 2 = 1 := by
            have hf : follows n (w.take 1) := follows_take w 1 hw
            simpa [htake, hb, follows] using hf
          have hexp : exponentsAfter (w.take 1) = ⟨3, 0, 2⟩ := by
            simp [htake, hb, exponentsAfter_odd_nil]
          have himg : image n (w.take 1) = floorPower n := by
            simp [htake, hb, image]
          have hcube : n ^ 3 < (floorPower n + 1) ^ 2 := odd_cube_lt_succ_sq hodd
          simpa [hexp, himg, pow_zero, one_mul] using hcube
      | succ k' =>
          have hk' : 0 < k' + 1 := Nat.succ_pos _
          have hk'le : k' + 1 ≤ w.length := Nat.le_of_succ_le hk
          have hih := ih hk' hk'le
          have hlt : k' + 1 < w.length := Nat.lt_of_succ_le hk
          have hsplit := take_succ_append (k := k' + 1) hlt
          have hexp := exponentsAfter_take_succ (k := k' + 1) hlt
          have hx : image n (w.take (k' + 1)) = floorPower^[k' + 1] n :=
            image_take_of_le hk'le
          have hge : n ≤ image n (w.take (k' + 1)) := by
            simpa [hx] using hmin (k' + 1) hlt
          have hf1 : follows n (w.take (k' + 2)) := follows_take w (k' + 2) hw
          have hf1' : follows n (w.take (k' + 1) ++ [w[k' + 1]]) := by
            rwa [← hsplit]
          have hlet : follows (image n (w.take (k' + 1))) [w[k' + 1]] :=
            follows_of_append_right hf1'
          have hpref : (w.take (k' + 1)).head? = some .odd := by
            cases w with
            | nil => exact (hwne rfl).elim
            | cons b rest =>
                have hb : b = .odd := by simpa [List.head?] using h0
                rw [List.take_succ_cons]
                simp [hb, List.head?]
          have ⟨hγeq, _hAeq⟩ := exponents_starts_odd (w := w.take (k' + 1)) hpref
          have hγ0 : (exponentsAfter (w.take (k' + 1))).gamma ≠ 0 := by
            rw [hγeq]
            exact two_pow_ne_zero _
          set s := exponentsAfter (w.take (k' + 1))
          set x := image n (w.take (k' + 1))
          have hchain : n ^ s.A < (n + 1) ^ s.B * (x + 1) ^ s.gamma := hih
          cases hb : w[k' + 1] with
          | even =>
              have heven : x % 2 = 0 := by
                simpa [hb, follows, x] using hlet
              have hstep :=
                absorb_even_step hn hchain hge heven hγ0
              have hexp' : exponentsAfter (w.take (k' + 2)) =
                  absorbEvenExponents s := by
                rw [hexp, hb]
              have habs : absorbEvenExponents s =
                  ⟨s.A + s.gamma, s.B + s.gamma, 2 * s.gamma⟩ :=
                absorbEven_struct s hγ0
              have himg' : image n (w.take (k' + 2)) = floorPower x := by
                rw [hsplit, image_append]
                simp [image, x]
              rw [hexp', habs, himg']
              exact hstep
          | odd =>
              have hodd : x % 2 = 1 := by
                simpa [hb, follows, x] using hlet
              have hlen_take : (w.take (k' + 1)).length = k' + 1 :=
                List.length_take_of_le hk'le
              have hγpow : s.gamma = 2 ^ (k' + 1) := by
                simpa [s, hlen_take] using hγeq
              have h3 : s.gamma % 3 ≠ 0 := by
                rw [hγpow]
                exact two_pow_not_mod_three _
              have hsc :=
                raise_chain (n := n) (x := x) (A := s.A) (B := s.B)
                  (γ := s.gamma) (k := 3) (by decide) hchain
              have hstep :=
                absorb_odd_step (n := n) (x := x) (A := 3 * s.A)
                  (B := 3 * s.B) (t := s.gamma) hn
                  (by
                    have : 3 * s.gamma = s.gamma * 3 := Nat.mul_comm _ _
                    simpa [this] using hsc)
                  hge hodd hγ0
              have hexp' : exponentsAfter (w.take (k' + 2)) =
                  absorbOddExponents s := by
                rw [hexp, hb]
              have habs : absorbOddExponents s =
                  ⟨3 * s.A + 3 * s.gamma, 3 * s.B + 3 * s.gamma,
                    2 * s.gamma⟩ :=
                absorbOdd_struct s hγ0 h3
              have himg' : image n (w.take (k' + 2)) = floorPower x := by
                rw [hsplit, image_append]
                simp [image, x]
              rw [hexp', habs, himg']
              exact hstep

theorem plus_one_chain {n : ℕ} {pref : List Branch}
    (hn : 1 ≤ n) (h0 : pref.head? = some .odd) (hne : pref ≠ [])
    (hw : follows n pref)
    (hmin : ∀ j, j < pref.length → n ≤ floorPower^[j] n) :
    let s := exponentsAfter pref
    n ^ s.A < (n + 1) ^ s.B * (image n pref + 1) ^ s.gamma := by
  have hlen : 0 < pref.length := List.length_pos_of_ne_nil hne
  have htake : pref.take pref.length = pref := List.take_length
  simpa [htake] using
    plus_one_chain_take hn h0 hw hmin pref.length hlen le_rfl

/-! ## Comparison at n ≥ 30 -/

theorem pow31_100_lt_pow30_101 : (31 : ℕ) ^ 100 < 30 ^ 101 := by
  native_decide

theorem pow31_66_lt_pow30_68 : (31 : ℕ) ^ 66 < 30 ^ 68 := by
  native_decide

theorem one_zero_one_mul_137 : (101 : ℕ) * 137 = 13837 := rfl

theorem one_three_eight_three_seven_add_68 : (13837 : ℕ) + 68 = 13905 := rfl

theorem one_zero_zero_mul_137_add_66 : (100 : ℕ) * 137 + 66 = 13766 := rfl

theorem one_three_nine_add_13766 : (139 : ℕ) + 13766 = 13905 := rfl

theorem thirteen_nine_zero_five_sub_139 : (13905 : ℕ) - 139 = 13766 := rfl

theorem pow31_13766_lt_pow30_13905 : (31 : ℕ) ^ 13766 < 30 ^ 13905 := by
  have h100 := pow31_100_lt_pow30_101
  have h66 := pow31_66_lt_pow30_68
  have hL : ((31 : ℕ) ^ 100) ^ 137 < (30 ^ 101) ^ 137 :=
    Nat.pow_lt_pow_left h100 (by decide : (137 : ℕ) ≠ 0)
  have hsplit : (31 : ℕ) ^ 13766 = ((31 : ℕ) ^ 100) ^ 137 * 31 ^ 66 := by
    rw [← one_zero_zero_mul_137_add_66, Nat.pow_add, Nat.pow_mul]
  have hleft : ((31 : ℕ) ^ 100) ^ 137 * 31 ^ 66 <
      (30 ^ 101) ^ 137 * 30 ^ 68 :=
    Nat.mul_lt_mul_of_lt_of_lt hL h66
  have hR : (30 ^ 101) ^ 137 * 30 ^ 68 = 30 ^ 13905 := by
    rw [← Nat.pow_mul, ← Nat.pow_add, one_zero_one_mul_137,
      one_three_eight_three_seven_add_68]
  exact (hsplit ▸ hleft).trans_eq hR

theorem succ_pow13766_lt_of_ge_30 {n : ℕ} (hn : 30 ≤ n) :
    (n + 1) ^ 13766 < n ^ 13905 := by
  have hlin : 30 * (n + 1) ≤ 31 * n := by omega
  have hpow : (30 * (n + 1)) ^ 13766 ≤ (31 * n) ^ 13766 :=
    Nat.pow_le_pow_left hlin 13766
  rw [mul_pow, mul_pow] at hpow
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 30) hn
  have hstrict : (31 : ℕ) ^ 13766 * n ^ 13766 < 30 ^ 13905 * n ^ 13766 :=
    Nat.mul_lt_mul_of_pos_right pow31_13766_lt_pow30_13905 (pow_pos hn0 13766)
  have hmid : (30 : ℕ) ^ 13766 * (n + 1) ^ 13766 < 30 ^ 13905 * n ^ 13766 :=
    lt_of_le_of_lt hpow hstrict
  have hsplit : (30 : ℕ) ^ 13905 = 30 ^ 139 * 30 ^ 13766 := by
    rw [← Nat.pow_add, one_three_nine_add_13766]
  have hRHS : (30 : ℕ) ^ 13905 * n ^ 13766 =
      30 ^ 13766 * (30 ^ 139 * n ^ 13766) := by
    rw [hsplit, mul_assoc, mul_left_comm (30 ^ 139)]
  have hpos : 0 < (30 : ℕ) ^ 13766 := pow_pos (by decide : (0 : ℕ) < 30) 13766
  have hcancel : (n + 1) ^ 13766 < 30 ^ 139 * n ^ 13766 :=
    (Nat.mul_lt_mul_left hpos).mp (hmid.trans_eq hRHS)
  have hn139 : (30 : ℕ) ^ 139 ≤ n ^ 139 := Nat.pow_le_pow_left hn 139
  have hle : (30 : ℕ) ^ 139 * n ^ 13766 ≤ n ^ 139 * n ^ 13766 :=
    Nat.mul_le_mul_right _ hn139
  have h13905 : n ^ 139 * n ^ 13766 = n ^ 13905 := by
    rw [← Nat.pow_add, one_three_nine_add_13766]
  exact hcancel.trans_le (hle.trans_eq h13905)

theorem succ_pow_slack139_of_ge_30 {n A : ℕ} (hn : 30 ≤ n)
    (hA : A ≤ 13905) (h139 : 139 ≤ A) :
    (n + 1) ^ (A - 139) < n ^ A := by
  set R := A - 139
  have hR : R ≤ 13766 :=
    (Nat.sub_le_sub_right hA 139).trans_eq thirteen_nine_zero_five_sub_139
  have hsum : 139 + R = A := Nat.add_sub_of_le h139
  have hrest : R + (13766 - R) = 13766 := Nat.add_sub_of_le hR
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 30) hn
  have hbig := succ_pow13766_lt_of_ge_30 hn
  have hmul :
      (n + 1) ^ R * n ^ (13766 - R) ≤
        (n + 1) ^ R * (n + 1) ^ (13766 - R) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) _)
  have hjoin : (n + 1) ^ R * (n + 1) ^ (13766 - R) = (n + 1) ^ 13766 := by
    rw [← Nat.pow_add, hrest]
  have hlt : (n + 1) ^ R * n ^ (13766 - R) < n ^ 13905 :=
    lt_of_le_of_lt (hmul.trans_eq hjoin) hbig
  have hright : n ^ 13905 = n ^ A * n ^ (13766 - R) := by
    have : 13905 = A + (13766 - R) := by omega
    rw [this, Nat.pow_add]
  rw [hright] at hlt
  have hpos : 0 < n ^ (13766 - R) := pow_pos hn0 _
  exact (Nat.mul_lt_mul_right hpos).mp hlt

/-! ## Finite pin and itinerary table -/

theorem fudge_words_ready :
    fudgeWords.all fudgeReady = true := by
  native_decide

theorem of_fudge_ready {w : List Branch} (hw : w ∈ fudgeWords) :
    fudgeReady w = true :=
  List.all_eq_true.mp fudge_words_ready w hw

theorem fudgeReady_dest {w : List Branch} (h : fudgeReady w = true) :
    w.head? = some .odd ∧
      w.getLast? = some .even ∧
        oddCount w = 7 ∧
          w.length = 11 ∧
            (exponentsAfter (dropTrailingEvens w)).A ≤ 13905 ∧
              1 ≤ trailingEvenCount w ∧
                noFollowsFrom2Below (dropTrailingEvens w) 30 = true ∧
                  dropTrailingEvens w ≠ [] := by
  simp [fudgeReady] at h
  tauto

theorem no_follows_from2_below {w : List Branch} {N n : ℕ}
    (hn2 : 2 ≤ n) (hn : n < N)
    (h : noFollowsFrom2Below w N = true) : ¬follows n w := by
  have hmem : n ∈ List.range N := List.mem_range.mpr hn
  intro hfollows
  have htrue : followsB n w = true := (followsB_iff n w).mpr hfollows
  have hall := List.all_eq_true.mp h n hmem
  simp [htrue] at hall
  omega

/-! ## CycleMin exclusion -/

theorem pref_oddCount_of_trailing (w : List Branch) :
    oddCount (dropTrailingEvens w) = oddCount w := by
  conv_rhs => rw [split_trailing_evens w]
  rw [oddCount_append, oddCount_replicate_even, Nat.add_zero]

theorem plus_one_vs_trailing {n : ℕ} {pref : List Branch} {r : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (h0 : pref.head? = some .odd)
    (hne : pref ≠ [])
    (h : CycleMin n (pref ++ List.replicate r Branch.even)) :
    let s := exponentsAfter pref
    n ^ s.A < (n + 1) ^ (s.B + s.gamma * 2 ^ r) := by
  have hw : follows n pref :=
    follows_of_append_left h.1.1
  have hlenp : pref.length <
      (pref ++ List.replicate r Branch.even).length := by
    simp
    omega
  have hmin : ∀ j, j < pref.length → n ≤ floorPower^[j] n := by
    intro j hj
    exact cycleMin_ge h (lt_trans hj hlenp)
  have hchain := plus_one_chain hn h0 hne hw hmin
  have hcell :=
    cycle_trailing_evens_lt (n := n) (v := pref) (r := r) hr h.1
  have hsucc : image n pref + 1 ≤ (n + 1) ^ (2 ^ r) :=
    Nat.succ_le_of_lt hcell
  set s := exponentsAfter pref
  have hpow :
      (image n pref + 1) ^ s.gamma ≤ ((n + 1) ^ (2 ^ r)) ^ s.gamma :=
    Nat.pow_le_pow_left hsucc _
  have hexp : ((n + 1) ^ (2 ^ r)) ^ s.gamma = (n + 1) ^ (s.gamma * 2 ^ r) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have hle :
      (n + 1) ^ s.B * (image n pref + 1) ^ s.gamma ≤
        (n + 1) ^ s.B * (n + 1) ^ (s.gamma * 2 ^ r) :=
    Nat.mul_le_mul_left _ (hpow.trans_eq hexp)
  have hjoin :
      (n + 1) ^ s.B * (n + 1) ^ (s.gamma * 2 ^ r) =
        (n + 1) ^ (s.B + s.gamma * 2 ^ r) :=
    (Nat.pow_add _ _ _).symm
  exact hchain.trans_le (hle.trans_eq hjoin)

theorem four_even_length {w : List Branch} (he : evenCount w = 4) :
    w.length = oddCount w + 4 := by
  have := evenCount_add_oddCount w
  omega

theorem slack_of_four_even_word {w : List Branch}
    (h0 : (dropTrailingEvens w).head? = some .odd)
    (he : evenCount w = 4) (ho : 7 ≤ oddCount w) :
    let pref := dropTrailingEvens w
    let r := trailingEvenCount w
    (exponentsAfter pref).A =
      (exponentsAfter pref).B + (exponentsAfter pref).gamma * 2 ^ r +
        familySlack (oddCount w) := by
  have hoddP : oddCount (dropTrailingEvens w) = oddCount w :=
    pref_oddCount_of_trailing w
  have hlen : (dropTrailingEvens w).length + trailingEvenCount w =
      oddCount w + 4 := by
    have hsplit := congrArg List.length (split_trailing_evens w)
    simp at hsplit
    have := four_even_length he
    omega
  simpa [hoddP] using slack_of_four_even h0 hoddP hlen ho

theorem slack139_of_seven_odd_length_eleven {pref : List Branch} {r : ℕ}
    (h0 : pref.head? = some .odd) (hodd : oddCount pref = 7)
    (hlen : pref.length + r = 11) :
    let s := exponentsAfter pref
    s.A = s.B + s.gamma * 2 ^ r + 139 := by
  have hlen' : pref.length + r = 7 + 4 := by
    simpa using hlen
  simpa [familySlack_seven] using
    slack_of_four_even h0 hodd hlen' (by decide : (7 : ℕ) ≤ 7)

theorem no_cycleMin_slack139 {n : ℕ} {w : List Branch}
    (hready : fudgeReady w = true) (h : CycleMin n w) : False := by
  obtain ⟨h0, _, hodd7, hlen11, hA, hr1, hpin, hne⟩ := fudgeReady_dest hready
  have hsplit := split_trailing_evens w
  have h0p : (dropTrailingEvens w).head? = some .odd := by
    have hw' := h0
    rw [hsplit] at hw'
    cases hd : dropTrailingEvens w with
    | nil => exact (hne hd).elim
    | cons _b _rest =>
        simpa [hd, List.head?] using hw'
  have hoddP : oddCount (dropTrailingEvens w) = 7 := by
    simpa [pref_oddCount_of_trailing] using hodd7
  have hlenP : (dropTrailingEvens w).length + trailingEvenCount w = 11 := by
    have := congrArg List.length hsplit
    simp [hlen11] at this
    omega
  have he4 : 1 ≤ evenCount w := by
    have : evenCount w + oddCount w = w.length := evenCount_add_oddCount w
    omega
  have hn2 : 2 ≤ n := by
    match n with
    | 0 => exact (not_follows_zero_of_odd_head h0 h.1.1).elim
    | 1 => exact (not_follows_one_of_even he4 h.1.1).elim
    | _n + 2 => omega
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn2
  have hC : CycleMin n
      (dropTrailingEvens w ++
        List.replicate (trailingEvenCount w) Branch.even) := by
    simpa [← hsplit] using h
  have hcmp := plus_one_vs_trailing hn1 hr1 h0p hne hC
  have hslack := slack139_of_seven_odd_length_eleven h0p hoddP hlenP
  set s := exponentsAfter (dropTrailingEvens w)
  have hright : s.B + s.gamma * 2 ^ trailingEvenCount w = s.A - 139 := by
    have h139 : 139 ≤ s.A := by
      have : s.A = s.B + s.gamma * 2 ^ trailingEvenCount w + 139 := hslack
      omega
    omega
  have hlt : n ^ s.A < (n + 1) ^ (s.A - 139) := by
    simpa [hright] using hcmp
  have h139 : 139 ≤ s.A := by
    have : s.A = s.B + s.gamma * 2 ^ trailingEvenCount w + 139 := hslack
    omega
  cases lt_or_ge n 30 with
  | inl hltn =>
      have hf : follows n (dropTrailingEvens w) :=
        follows_of_append_left hC.1.1
      exact no_follows_from2_below hn2 hltn hpin hf
  | inr hge =>
      have hgeA : (n + 1) ^ (s.A - 139) < n ^ s.A :=
        succ_pow_slack139_of_ge_30 hge hA h139
      exact (not_lt_of_ge (le_of_lt hgeA)).elim hlt

/-- The thirty first-expanding short-gap leftovers are not `CycleMin`
words. Not a length-11 census. -/
theorem no_cycleMin_cyclemin_fudge {n : ℕ} {w : List Branch}
    (hw : w ∈ fudgeWords) (h : CycleMin n w) : False :=
  no_cycleMin_slack139 (of_fudge_ready hw) h

/-! ## Unique-rotation CycleItinerary upgrade -/

theorem rotate_eq_of_only_self {w : List Branch} {k : ℕ}
    (hu : onlySelfCycleMinShape w = true) (hk : k < w.length)
    (hshape : startsTwoOddsEndsEven (rotateItinerary w k) = true) :
    rotateItinerary w k = w := by
  have hmem : k ∈ List.range w.length := List.mem_range.mpr hk
  have hall := List.all_eq_true.mp hu k hmem
  simp [hshape] at hall
  exact hall

theorem startsTwoOddsEndsEven_of_cycleMin {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    startsTwoOddsEndsEven w = true := by
  have ⟨rest, hw⟩ := cycleMin_starts_two_odds hn h
  have hend := cycleMin_getLast_even hn h
  have hhead : w.head? = some .odd := by
    simp [hw, List.head?]
  have h1 : w[1]?.getD Branch.even = Branch.odd := by
    simp [hw]
  simp [startsTwoOddsEndsEven, hhead, h1, hend]

theorem no_cycle_itinerary_of_unique_fudge {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : w ∈ fudgeWords)
    (hu : onlySelfCycleMinShape w = true)
    (h : CycleItinerary n w) : False := by
  obtain ⟨k, hk, hm⟩ := exists_cycleMin hn h
  have hnk : 2 ≤ floorPower^[k] n := cycleItinerary_iterate_ge_two hn h hk
  have hshape := startsTwoOddsEndsEven_of_cycleMin hnk hm
  have heq := rotate_eq_of_only_self hu hk hshape
  exact no_cycleMin_cyclemin_fudge hw (by simpa [heq] using hm)

/-! ## Named corollaries

`no_cycleMin_*` for every first-expanding leftover. `no_cycle_itinerary_*`
only when the leftover is its unique CycleMin-shaped rotation.
`OOOOOOOEEEE` is already `no_cycle_itinerary_oooooooeeee` in `O7EEEEGap`.
-/

theorem no_cycleMin_of_fourEven {n a0 a1 a2 a3 : ℕ}
    (hmem : fourEvenWord a0 a1 a2 a3 ∈ fudgeWords) :
    ¬CycleMin n (fourEvenWord a0 a1 a2 a3) :=
  fun h => no_cycleMin_cyclemin_fudge hmem h

theorem no_cycleMin_one_three_eee {n : ℕ} {a0 a1 : ℕ}
    (hmem : fourEvenWord a0 a1 0 0 ∈ fudgeWords) :
    ¬CycleMin n (fourEvenWord a0 a1 0 0) :=
  no_cycleMin_of_fourEven hmem

theorem no_cycleMin_oooooooeeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 7 0 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooooeoeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 6 1 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooooeooeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 5 2 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeoooeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 3 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeooooeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 4 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeoooooeee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 5 0 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooooeeeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 6 0 0 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooooeoeeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 5 1 0 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeooeeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 2 0 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeoooeeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 3 0 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeooooeeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 4 0 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooooeeoee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 6 0 1 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooooeoeoee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 5 1 1 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeooeoee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 2 1 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeoooeoee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 3 1 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeooooeoee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 4 1 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooooeeoeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 5 0 1 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeoeoeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 1 1 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeooeoeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 2 1 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeoooeoeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 3 1 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooooeeooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 5 0 2 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeoeooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 1 2 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeooeooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 2 2 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeoooeooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 3 2 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeeooeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 0 2 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeoeooeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 1 2 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeooeooeoe {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 2 2 1) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooooeeoooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 4 0 3 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_oooeoeoooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 3 1 3 0) :=
  no_cycleMin_of_fourEven (by decide)
theorem no_cycleMin_ooeooeoooee {n : ℕ} :
    ¬CycleMin n (fourEvenWord 2 2 3 0) :=
  no_cycleMin_of_fourEven (by decide)

theorem unique_ooooooeoeee :
    onlySelfCycleMinShape (fourEvenWord 6 1 0 0) = true := by native_decide
theorem unique_ooooooeeeoe :
    onlySelfCycleMinShape (fourEvenWord 6 0 0 1) = true := by native_decide
theorem unique_oooooeoeeoe :
    onlySelfCycleMinShape (fourEvenWord 5 1 0 1) = true := by native_decide
theorem unique_ooooooeeoee :
    onlySelfCycleMinShape (fourEvenWord 6 0 1 0) = true := by native_decide
theorem unique_oooooeoeoee :
    onlySelfCycleMinShape (fourEvenWord 5 1 1 0) = true := by native_decide
theorem unique_oooooeeoeoe :
    onlySelfCycleMinShape (fourEvenWord 5 0 1 1) = true := by native_decide
theorem unique_ooooeoeoeoe :
    onlySelfCycleMinShape (fourEvenWord 4 1 1 1) = true := by native_decide

theorem no_cycle_itinerary_ooooooeoeee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 1 0 0) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_ooooooeoeee h
theorem no_cycle_itinerary_ooooooeeeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 0 0 1) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_ooooooeeeoe h
theorem no_cycle_itinerary_oooooeoeeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 1 0 1) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_oooooeoeeoe h
theorem no_cycle_itinerary_ooooooeeoee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 6 0 1 0) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_ooooooeeoee h
theorem no_cycle_itinerary_oooooeoeoee {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 1 1 0) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_oooooeoeoee h
theorem no_cycle_itinerary_oooooeeoeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 5 0 1 1) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_oooooeeoeoe h
theorem no_cycle_itinerary_ooooeoeoeoe {n : ℕ} (hn : 2 ≤ n) :
    ¬CycleItinerary n (fourEvenWord 4 1 1 1) :=
  fun h => no_cycle_itinerary_of_unique_fudge hn (by decide) unique_ooooeoeoeoe h

end Problems.Juggler
