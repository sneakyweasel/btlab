import Problems.Juggler.CycleMinOOOSquare
import Problems.Juggler.Progress

namespace Problems.Juggler.CycleMinEnvelopes

open Problems.Juggler Problems.Juggler.OOOSquare

/-!
# Power envelopes along the post-L corridor

Here `L = OOEOOOEOOEE` (length 11, seven odds), `M = L·OOE` (length 14, nine
odds) and `W₅ = M·(OOE)^5` (length 29, nineteen odds). Every bound below is
`power_bound_word` on a realized word, `x^{2^{|w|}} ≤ n^{3^{#O(w)}}`, followed
by a cell comparison `3^{#O} < k·2^{|w|}` giving `x < n^k`. Negative
comparisons record where the envelope does not certify a cell or a drop;
they are statements about this method, not about the orbit. Starting `L`, or
its `OOE·OOO` entrance, needs an odd state, so an even state cannot start
it. These are corridor budgets, not halting theorems.
-/

/-- The word `L = OOEOOOEOOEE`. -/
def lWord : List Branch :=
  [.odd, .odd, .even, .odd, .odd, .odd, .even, .odd, .odd, .even, .even]

/-- The word `M = L·OOE = OOEOOOEOOEEOOE`. -/
def mWord : List Branch := lWord ++ [.odd, .odd, .even]

/-- The word `W₅ = M·(OOE)^5`. -/
def w5Word : List Branch := mWord ++ ooePow 5

/-- The `OOE·OOO` entrance of `L`. -/
def lEntrance : List Branch := [.odd, .odd, .even, .odd, .odd, .odd]

/-- Cell form of the envelope: a realized word with `3^{#O} < k·2^{|w|}`
lands below `n^k`. -/
theorem image_lt_of_gap {n k : ℕ} {w : List Branch} (hn : 2 ≤ n)
    (hw : follows n w) (hgap : 3 ^ oddCount w < k * 2 ^ w.length) :
    image n w < n ^ k := by
  have h := power_bound_word hw
  rw [image_eq_iterate]
  exact envelope_lt_pow hn (by positivity) h hgap

/-- Half-cell form after a final even letter: if `w = u·E` and
`3^{#O(w)} < k·2^{|u|}`, then `image^2 < n^k`. -/
theorem image_sq_lt_of_gap {n k : ℕ} {u : List Branch} (hn : 2 ≤ n)
    (hw : follows n (u ++ [.even])) (hgap : 3 ^ oddCount u < k * 2 ^ u.length) :
    image n (u ++ [.even]) ^ 2 < n ^ k := by
  have h := power_bound_word hw
  have hlen : (u ++ [Branch.even]).length = u.length + 1 := by simp
  have hodd : oddCount (u ++ [Branch.even]) = oddCount u := by
    simp [oddCount_append]
  have himg : image n (u ++ [.even]) = floorPower^[u.length + 1] n := by
    rw [image_eq_iterate, hlen]
  rw [hlen, hodd, ← himg] at h
  have h' : (image n (u ++ [.even]) ^ 2) ^ (2 ^ u.length) ≤ n ^ 3 ^ oddCount u := by
    calc (image n (u ++ [.even]) ^ 2) ^ (2 ^ u.length)
        = image n (u ++ [.even]) ^ (2 ^ (u.length + 1)) := by
          rw [← pow_mul, pow_succ]; ring_nf
      _ ≤ _ := h
  exact envelope_lt_pow hn (by positivity) h' hgap

/-- Composition of envelopes: if `t^A ≤ n^B` and `t` realizes `W` with
`B·3^{#O(W)} < A·2^{|W|}`, then `T_W(t) < n`. -/
theorem compose_lt {n t A B : ℕ} {W : List Branch} (hn : 2 ≤ n) (hA : 0 < A)
    (ht : t ^ A ≤ n ^ B) (hW : follows t W)
    (hgap : B * 3 ^ oddCount W < A * 2 ^ W.length) : image t W < n := by
  have h := power_bound_word hW
  rw [← image_eq_iterate] at h
  have hc : image t W ^ (A * 2 ^ W.length) ≤ n ^ (B * 3 ^ oddCount W) := by
    calc image t W ^ (A * 2 ^ W.length) = (image t W ^ 2 ^ W.length) ^ A := by
          rw [← pow_mul, mul_comm]
      _ ≤ (t ^ 3 ^ oddCount W) ^ A := Nat.pow_le_pow_left h A
      _ = (t ^ A) ^ 3 ^ oddCount W := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (n ^ B) ^ 3 ^ oddCount W := Nat.pow_le_pow_left ht _
      _ = n ^ (B * 3 ^ oddCount W) := by rw [← pow_mul]
  have := envelope_lt_pow (k := 1) hn (by positivity) hc (by simpa using hgap)
  simpa using this

/-- The composed envelope exponent pair, without a cell conclusion. -/
theorem compose_bound {n t A B : ℕ} {W : List Branch} (ht : t ^ A ≤ n ^ B)
    (hW : follows t W) :
    image t W ^ (A * 2 ^ W.length) ≤ n ^ (B * 3 ^ oddCount W) := by
  have h := power_bound_word hW
  rw [← image_eq_iterate] at h
  calc image t W ^ (A * 2 ^ W.length) = (image t W ^ 2 ^ W.length) ^ A := by
        rw [← pow_mul, mul_comm]
    _ ≤ (t ^ 3 ^ oddCount W) ^ A := Nat.pow_le_pow_left h A
    _ = (t ^ A) ^ 3 ^ oddCount W := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (n ^ B) ^ 3 ^ oddCount W := Nat.pow_le_pow_left ht _
    _ = n ^ (B * 3 ^ oddCount W) := by rw [← pow_mul]

/-- An even state cannot start any word beginning with an odd letter. -/
theorem not_follows_odd_head_of_even {x : ℕ} {w : List Branch} (hx : x % 2 = 0) :
    ¬ follows x (.odd :: w) := fun h => by have := h.1; omega

/-- A state realizing `OE` cannot start `OO`. -/
theorem not_follows_oo_of_oe {x : ℕ} {w : List Branch}
    (hx : follows x [.odd, .even]) : ¬ follows x (.odd :: .odd :: w) := by
  intro h
  have h1 := hx.2.1
  have h2 := h.2.1
  omega

/-! ## Post-L envelope `t^{2048} ≤ n^{2187}` -/

/-- After `L`, `t = T_L(n)` satisfies `t^{2048} ≤ n^{2187}`. -/
theorem post_l_bound {n : ℕ} (hw : follows n lWord) :
    image n lWord ^ 2048 ≤ n ^ 2187 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  simpa [lWord, oddCount] using h

/-- The post-L exponent test cannot certify descent after an odd run:
`2187·3^k < 2048·2^k` fails for every `k`, with slack `139` at `k = 0`
and strictly increasing slack. -/
theorem post_l_odd_run_exponent_not_lt (k : ℕ) : ¬ 2187 * 3 ^ k < 2048 * 2 ^ k := by
  have : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  omega

/-- The envelope premise and a failed exponent test are compatible with actual
descent: the odd step from `3` is `5`, below the anchor `6`. -/
theorem post_l_envelope_descent_example :
    (3 : ℕ) ^ 2048 ≤ 6 ^ 2187 ∧ follows 3 [.odd] ∧
      image 3 [.odd] = 5 ∧ image 3 [.odd] < 6 ∧ ¬ 2187 * 3 ^ 1 < 2048 * 2 ^ 1 := by
  have bound (a b m n : ℕ) (hab : a ≤ b) (hb : 1 ≤ b) (hmn : m ≤ n) :
      a ^ m ≤ b ^ n :=
    (Nat.pow_le_pow_left hab m).trans (Nat.pow_le_pow_right hb hmn)
  exact ⟨bound 3 6 2048 2187 (by decide) (by decide) (by decide),
    by simp [follows], by decide +kernel, by decide +kernel, by norm_num⟩

/-- The slack `2187·3^k - 2048·2^k` is `139` at `k = 0`. -/
theorem odd_run_slack_zero : 2187 * 3 ^ 0 - 2048 * 2 ^ 0 = 139 := by norm_num

/-- The slack `2187·3^k - 2048·2^k` strictly increases with `k`. -/
theorem odd_run_slack_strictMono (k : ℕ) :
    2187 * 3 ^ k - 2048 * 2 ^ k < 2187 * 3 ^ (k + 1) - 2048 * 2 ^ (k + 1) := by
  have h : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ, pow_succ]
  omega

/-- Composing the post-L envelope with `O^k` gives exactly the exponent pair
`(2048·2^k, 2187·3^k)`, which never certifies a drop below `n`. -/
theorem post_l_odd_run_bound {n t k : ℕ} (ht : t ^ 2048 ≤ n ^ 2187)
    (hW : follows t (List.replicate k .odd)) :
    image t (List.replicate k .odd) ^ (2048 * 2 ^ k) ≤ n ^ (2187 * 3 ^ k) := by
  have := compose_bound ht hW
  simpa [oddCount_replicate_odd] using this

/-- One-shot post-L drops: any further `W` with `2187·3^{#O} < 2048·2^{|W|}`
lands below `n`; an even `t` (`W = E`) and a `t` realizing `OE` drop. -/
theorem post_l_drop {n t : ℕ} {W : List Branch} (hn : 2 ≤ n)
    (ht : t ^ 2048 ≤ n ^ 2187) (hW : follows t W)
    (hgap : 2187 * 3 ^ oddCount W < 2048 * 2 ^ W.length) : image t W < n :=
  compose_lt hn (by norm_num) ht hW hgap

/-- An even post-L state drops below `n` after one E (`2187 < 4096`). -/
theorem post_l_drop_even {n t : ℕ} (hn : 2 ≤ n) (ht : t ^ 2048 ≤ n ^ 2187)
    (he : t % 2 = 0) : image t [.even] < n :=
  post_l_drop hn ht ⟨he, trivial⟩ (by decide)

/-- A post-L state realizing `OE` drops below `n` (`6561 < 8192`). -/
theorem post_l_drop_oe {n t : ℕ} (hn : 2 ≤ n) (ht : t ^ 2048 ≤ n ^ 2187)
    (hW : follows t [.odd, .even]) : image t [.odd, .even] < n :=
  post_l_drop hn ht hW (by decide)

/-- The post-L `OOE` exponent test cannot certify descent below `n`. -/
theorem post_l_ooe_exponent_not_lt : ¬ 2187 * 3 ^ 2 < 2048 * 2 ^ 3 := by norm_num

/-- A second copy of `L` fails the envelope descent test (`2187^2 > 2048^2`). -/
theorem post_l_second_l_exponent_not_lt :
    ¬ 2187 * 3 ^ oddCount lWord < 2048 * 2 ^ lWord.length := by decide

/-! ## The composite `M = L·OOE` -/

/-- `s = T_M(n)` satisfies `s^{16384} ≤ n^{19683}`, hence `s < n^2`. -/
theorem m_bound {n : ℕ} (hw : follows n mWord) :
    image n mWord ^ 16384 ≤ n ^ 19683 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  simpa [mWord, lWord, oddCount] using h

/-- `T_M(n) < n^2`, from `19683 < 2·16384`. -/
theorem m_lt_sq {n : ℕ} (hn : 2 ≤ n) (hw : follows n mWord) : image n mWord < n ^ 2 :=
  image_lt_of_gap hn hw (by decide)

/-- The exponent test for `M` fails; this does not rule out actual descent. -/
theorem m_exponent_not_lt : ¬ 3 ^ oddCount mWord < 2 ^ mWord.length := by decide

/-- `M·E` and `M·OE` contract versus `n`, giving finite progress. -/
theorem me_finiteProgress {n : ℕ} (hn : 2 ≤ n) (hw : follows n (mWord ++ [.even])) :
    FiniteProgress n :=
  finiteProgress_of_imageLt hw (by simpa using image_lt_of_gap (k := 1) hn hw (by decide))

/-- `M·OE` contracts versus `n` (`59049 < 65536`), giving finite progress. -/
theorem moe_finiteProgress {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n (mWord ++ [.odd, .even])) : FiniteProgress n :=
  finiteProgress_of_imageLt hw (by simpa using image_lt_of_gap (k := 1) hn hw (by decide))

/-- Neither contracting landing can meet the `OOE·OOO` entrance of `L`. -/
theorem even_not_lEntrance {s : ℕ} (hs : s % 2 = 0) : ¬ follows s lEntrance :=
  not_follows_odd_head_of_even hs

/-- A state realizing `OE` cannot meet the `OOE·OOO` entrance of `L`. -/
theorem oe_not_lEntrance {s : ℕ} (hs : follows s [.odd, .even]) : ¬ follows s lEntrance :=
  not_follows_oo_of_oe hs

/-- A second post-L `OOE` followed by `OE` fails the envelope descent test (`3^12 > 2^19`). -/
theorem m_ooe_oe_exponent_not_lt :
    ¬ 3 ^ oddCount (mWord ++ ([.odd, .odd, .even, .odd, .even] : List Branch)) <
      2 ^ (mWord ++ ([.odd, .odd, .even, .odd, .even] : List Branch)).length := by decide

/-! ## `M·(OOE)^k` and the second post-L `OOE` -/

/-- `|M·(OOE)^k| = 14 + 3k`. -/
theorem m_ooePow_length (k : ℕ) : (mWord ++ ooePow k).length = 14 + 3 * k := by
  simp [ooePow_length, mWord, lWord]; omega

/-- `#O(M·(OOE)^k) = 9 + 2k`. -/
theorem m_ooePow_oddCount (k : ℕ) : oddCount (mWord ++ ooePow k) = 9 + 2 * k := by
  rw [oddCount_append, ooePow_oddCount]; rfl

/-- `M·(OOE)^k` keeps the square-cell gap `3^{9+2k} < 2^{15+3k}` iff `k ≤ 4`. -/
theorem m_ooePow_gap_iff (k : ℕ) : 3 ^ (9 + 2 * k) < 2 ^ (15 + 3 * k) ↔ k ≤ 4 := by
  constructor
  · intro h
    by_contra hk
    have hk5 : 5 ≤ k := by omega
    obtain ⟨j, rfl⟩ : ∃ j, k = 5 + j := ⟨k - 5, by omega⟩
    have hbase : 2 ^ 30 ≤ 3 ^ 19 := by norm_num
    have h89 : 8 ^ j ≤ 9 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have : 2 ^ (15 + 3 * (5 + j)) ≤ 3 ^ (9 + 2 * (5 + j)) := by
      calc 2 ^ (15 + 3 * (5 + j)) = 2 ^ 30 * 8 ^ j := by
            rw [show 15 + 3 * (5 + j) = 30 + 3 * j by ring, pow_add, pow_mul]; norm_num
        _ ≤ 3 ^ 19 * 9 ^ j := Nat.mul_le_mul hbase h89
        _ = 3 ^ (9 + 2 * (5 + j)) := by
            rw [show 9 + 2 * (5 + j) = 19 + 2 * j by ring, pow_add, pow_mul]; norm_num
    omega
  · intro hk
    interval_cases k <;> norm_num

/-- After `M·OOE` (length 17, eleven odds), `r^{2^17} ≤ n^{3^11}` and `r < n^2`. -/
theorem m_ooe_lt_sq {n : ℕ} (hn : 2 ≤ n) (hw : follows n (mWord ++ ooePow 1)) :
    image n (mWord ++ ooePow 1) < n ^ 2 :=
  image_lt_of_gap hn hw (by rw [m_ooePow_oddCount, m_ooePow_length]; norm_num)

/-- From a cycle minimum with a proper `M·OOE` prefix, `n ≤ r < n^2`; an even
`r` gives finite progress (`3^11 < 2^18`); otherwise `v` starts with `O`. -/
theorem cycleMin_m_ooe {n : ℕ} {v : List Branch} (hn : 2 ≤ n) (hv : v ≠ [])
    (hmin : CycleMin n (mWord ++ ooePow 1 ++ v)) :
    (n ≤ image n (mWord ++ ooePow 1) ∧ image n (mWord ++ ooePow 1) < n ^ 2) ∧
      (FiniteProgress n ∨ v.head? = some .odd) := by
  have hfol : follows n (mWord ++ ooePow 1 ++ v) := hmin.1.1
  have hw : follows n (mWord ++ ooePow 1) := follows_of_append_left hfol
  refine ⟨⟨?_, m_ooe_lt_sq hn hw⟩, ?_⟩
  · rw [image_eq_iterate]
    apply cycleMin_ge hmin
    have : 0 < v.length := List.length_pos_of_ne_nil hv
    simp only [List.length_append]
    omega
  · obtain ⟨b, v', rfl⟩ := List.exists_cons_of_ne_nil hv
    cases b with
    | odd => exact Or.inr rfl
    | even =>
        left
        have he : follows n (mWord ++ ooePow 1 ++ [.even]) := by
          have := hfol
          rw [show mWord ++ ooePow 1 ++ Branch.even :: v' =
            (mWord ++ ooePow 1 ++ [.even]) ++ v' by simp] at this
          exact follows_of_append_left this
        exact finiteProgress_of_imageLt he
          (by simpa using image_lt_of_gap (k := 1) hn he (by decide))

/-! ## The `W₅` chain -/

/-- `|W₅| = 29`. -/
theorem w5_length : w5Word.length = 29 := by rw [w5Word, m_ooePow_length]
/-- `#O(W₅) = 19`. -/
theorem w5_oddCount : oddCount w5Word = 19 := by
  simp only [w5Word]; rw [m_ooePow_oddCount]

/-- `x₅ = T_{W₅}(n)` satisfies `x₅^{2^29} ≤ n^{3^19}`. -/
theorem w5_bound {n : ℕ} (hw : follows n w5Word) :
    image n w5Word ^ 2 ^ 29 ≤ n ^ 3 ^ 19 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate, w5_length, w5_oddCount] at h
  exact h

/-- Square cell fails, cube cell holds: `2^30 < 3^19 < 3·2^29`, so `x₅ < n^3`. -/
theorem w5_cells : 2 * 2 ^ 29 < 3 ^ 19 ∧ 3 ^ 19 < 3 * 2 ^ 29 := by norm_num

/-- `x₅ = T_{W₅}(n) < n^3`, from the cube cell `3^19 < 3·2^29`. -/
theorem w5_lt_cube {n : ℕ} (hn : 2 ≤ n) (hw : follows n w5Word) : image n w5Word < n ^ 3 :=
  image_lt_of_gap hn hw (by rw [w5_oddCount, w5_length]; norm_num)

/-- The `k = 4` ceiling is below 2, the `k = 5` ceiling above 2, and their
ratio is exactly `9/8`. -/
theorem w4_w5_ceilings : 3 ^ 17 < 2 * 2 ^ 26 ∧ 2 * 2 ^ 29 < 3 ^ 19 ∧
    3 ^ 19 * 2 ^ 26 * 8 = 3 ^ 17 * 2 ^ 29 * 9 := by norm_num

/-- Even `x₅`: `T(x₅)^2 < n^3`, so `T(x₅) < n^2`; `x₅` cannot start `L`;
and `3^19 > 2^30`, so the envelope gives no finite progress there. -/
theorem w5_even {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.even])) :
    image n (w5Word ++ [.even]) ^ 2 < n ^ 3 ∧ image n (w5Word ++ [.even]) < n ^ 2 ∧
      ¬ follows (image n w5Word) lWord := by
  have hsq := image_sq_lt_of_gap (k := 3) hn hw (by rw [w5_oddCount, w5_length]; norm_num)
  refine ⟨hsq, ?_, ?_⟩
  · have : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h4 : image n (w5Word ++ [.even]) ^ 2 < (n ^ 2) ^ 2 :=
      calc _ < n ^ 3 := hsq
        _ ≤ n ^ 4 := this
        _ = (n ^ 2) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h4
  · have he := (follows_of_append_right hw).1
    exact not_follows_odd_head_of_even he

/-- The exponent test does not certify a drop below the original anchor after
even `x₅` (`3^19 ≥ 2^30`). -/
theorem w5_even_exponent_not_lt : ¬ 3 ^ 19 < 2 ^ 30 := by norm_num

/-- Odd `x₅`: the next O lands below `n^4` (`3^20 < 4·2^30`). -/
theorem w5_odd_lt_fourth {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd])) :
    image n (w5Word ++ [.odd]) < n ^ 4 :=
  image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length])

/-! ### `y = T(x₅)` for odd `x₅` -/

/-- `y = T(x₅)` satisfies `y^{2^30} ≤ n^{3^20}`. -/
theorem y_bound {n : ℕ} (hw : follows n (w5Word ++ [.odd])) :
    image n (w5Word ++ [.odd]) ^ 2 ^ 30 ≤ n ^ 3 ^ 20 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  simpa [oddCount_append, w5_oddCount, w5_length] using h

/-- Cube cell fails, fourth-power cell holds, below the generic `9/2`. -/
theorem y_cells : 3 * 2 ^ 30 < 3 ^ 20 ∧ 3 ^ 20 < 4 * 2 ^ 30 ∧ 3 ^ 20 < 9 * 2 ^ 29 := by
  norm_num

/-- Even `y`: `z = T(y) < n^2`, `y` cannot start `L`, and `3^20 > 2^31`. -/
theorem y_even {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .even])) :
    image n (w5Word ++ [.odd, .even]) < n ^ 2 ∧
      ¬ follows (image n (w5Word ++ [.odd])) lWord := by
  refine ⟨image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length]), ?_⟩
  have h := hw
  rw [show w5Word ++ [Branch.odd, .even] = (w5Word ++ [.odd]) ++ [.even] by simp] at h
  exact not_follows_odd_head_of_even (follows_of_append_right h).1

/-- The exponent test does not certify a drop below the original anchor after
even `y` (`3^20 ≥ 2^31`). -/
theorem y_even_exponent_not_lt : ¬ 3 ^ 20 < 2 ^ 31 := by norm_num

/-- From `x₅`, `OEE` contracts versus `n` (`3^20 < 2^32`); `E`, `OE`, `OOE`
and `OOOE` fail that exponent test. -/
theorem x5_contractions :
    3 ^ 20 < 2 ^ 32 ∧ ¬ 3 ^ 19 < 2 ^ 30 ∧ ¬ 3 ^ 20 < 2 ^ 31 ∧
      ¬ 3 ^ 21 < 2 ^ 32 ∧ ¬ 3 ^ 22 < 2 ^ 33 := by norm_num

/-- `OEE` from `x₅` lands below `n` (`3^20 < 2^32`). -/
theorem x5_oee_drop {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .even, .even])) :
    image n (w5Word ++ [.odd, .even, .even]) < n := by
  simpa using image_lt_of_gap (k := 1) hn hw
    (by simp [oddCount_append, w5_oddCount, w5_length])

/-- A second O from odd `y` stays below `n^5` (`3^21 < 5·2^31`). -/
theorem y_odd_lt_fifth {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .odd])) :
    image n (w5Word ++ [.odd, .odd]) < n ^ 5 :=
  image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length])

/-! ### `z = T(y)` for odd `x₅, y` -/

/-- `z = T(y)` satisfies `z^{2^31} ≤ n^{3^21}`. -/
theorem z_bound {n : ℕ} (hw : follows n (w5Word ++ [.odd, .odd])) :
    image n (w5Word ++ [.odd, .odd]) ^ 2 ^ 31 ≤ n ^ 3 ^ 21 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  simpa [oddCount_append, w5_oddCount, w5_length] using h

/-- For `z`, the fourth-power cell fails and the fifth-power cell holds. -/
theorem z_cells : 4 * 2 ^ 31 < 3 ^ 21 ∧ 3 ^ 21 < 5 * 2 ^ 31 := by norm_num

/-- Generic odd-step comparison: `x < n^{2b}` gives `T(x) < n^{3b}` for odd `x`
(so `y < n^4 ⇒ z < n^6` and `u < n^8 ⇒ v < n^12`). -/
theorem floorPower_odd_lt_of_lt {x n b : ℕ} (hx : x % 2 = 1) (h : x < n ^ (2 * b)) :
    floorPower x < n ^ (3 * b) := by
  rw [floorPower_odd_eq hx, Nat.sqrt_lt']
  calc x ^ 3 < (n ^ (2 * b)) ^ 3 := Nat.pow_lt_pow_left h (by norm_num)
    _ = (n ^ (3 * b)) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf

/-- Even `z`: `T(z)^2 < n^5`, hence `T(z) < n^3`; `z` cannot start `L`; and
`3^21 > 2^33`, so even `z` is not certified below `n^2`. -/
theorem z_even {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .odd, .even])) :
    image n (w5Word ++ [.odd, .odd, .even]) ^ 2 < n ^ 5 ∧
      image n (w5Word ++ [.odd, .odd, .even]) < n ^ 3 ∧
      ¬ follows (image n (w5Word ++ [.odd, .odd])) lWord := by
  have hw' : follows n ((w5Word ++ [.odd, .odd]) ++ [.even]) := by simpa using hw
  have hsq := image_sq_lt_of_gap (k := 5) hn hw'
    (by simp [oddCount_append, w5_oddCount, w5_length])
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hsq
  refine ⟨hsq, ?_, ?_⟩
  · have : n ^ 5 ≤ n ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6 : image n (w5Word ++ [.odd, .odd, .even]) ^ 2 < (n ^ 3) ^ 2 :=
      calc _ < n ^ 5 := hsq
        _ ≤ n ^ 6 := this
        _ = (n ^ 3) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h6
  · exact not_follows_odd_head_of_even (follows_of_append_right hw').1

/-- Even `z` is not certified below `n^2` (`3^21 ≥ 2^33`). -/
theorem z_even_exponent_not_lt_two : ¬ 3 ^ 21 < 2 * 2 ^ 32 := by norm_num

/-- Odd `z`: `u = T(z)` satisfies `u^{2^32} ≤ n^{3^22}` and `u < n^8`. -/
theorem u_bound {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .odd, .odd])) :
    image n (w5Word ++ [.odd, .odd, .odd]) ^ 2 ^ 32 ≤ n ^ 3 ^ 22 ∧
      image n (w5Word ++ [.odd, .odd, .odd]) < n ^ 8 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  refine ⟨by simpa [oddCount_append, w5_oddCount, w5_length] using h, ?_⟩
  exact image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length])

/-- Even `u` returns below `n^4` (`3^22 < 4·2^33`). -/
theorem u_even_lt_fourth {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n (w5Word ++ [.odd, .odd, .odd, .even])) :
    image n (w5Word ++ [.odd, .odd, .odd, .even]) < n ^ 4 :=
  image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length])

/-! ### `v = T(u)` for odd `x₅, y, z, u` -/

/-- `v = T(u)` satisfies `v^{2^33} ≤ n^{3^23}` and `v < n^11`. -/
theorem v_bound {n : ℕ} (hn : 2 ≤ n) (hw : follows n (w5Word ++ [.odd, .odd, .odd, .odd])) :
    image n (w5Word ++ [.odd, .odd, .odd, .odd]) ^ 2 ^ 33 ≤ n ^ 3 ^ 23 ∧
      image n (w5Word ++ [.odd, .odd, .odd, .odd]) < n ^ 11 := by
  have h := power_bound_word hw
  rw [← image_eq_iterate] at h
  refine ⟨by simpa [oddCount_append, w5_oddCount, w5_length] using h, ?_⟩
  exact image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length])

/-- For `v`, the tenth-power cell fails and the eleventh-power cell holds. -/
theorem v_cells : 10 * 2 ^ 33 < 3 ^ 23 ∧ 3 ^ 23 < 11 * 2 ^ 33 := by norm_num

/-- Even `v`: `T(v) < n^6`; `3^23 > 4·2^34`, so not certified below `n^4`;
and `v` cannot start `L`. -/
theorem v_even {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n (w5Word ++ [.odd, .odd, .odd, .odd, .even])) :
    image n (w5Word ++ [.odd, .odd, .odd, .odd, .even]) < n ^ 6 ∧
      ¬ follows (image n (w5Word ++ [.odd, .odd, .odd, .odd])) lWord := by
  refine ⟨image_lt_of_gap hn hw (by simp [oddCount_append, w5_oddCount, w5_length]), ?_⟩
  have hw' : follows n ((w5Word ++ [.odd, .odd, .odd, .odd]) ++ [.even]) := by simpa using hw
  exact not_follows_odd_head_of_even (follows_of_append_right hw').1

/-- Even `v` is not certified below `n^4` (`3^23 ≥ 4·2^34`). -/
theorem v_even_exponent_not_lt_four : ¬ 3 ^ 23 < 4 * 2 ^ 34 := by norm_num

/-- After `W₅` plus `k` extra odds, the first integer cells are `3,4,5,8,11`
for `k = 0,…,4`: `(c-1)·2^{29+k} ≤ 3^{19+k} < c·2^{29+k}`. -/
theorem w5_extra_odd_cells :
    (2 * 2 ^ 29 ≤ 3 ^ 19 ∧ 3 ^ 19 < 3 * 2 ^ 29) ∧
    (3 * 2 ^ 30 ≤ 3 ^ 20 ∧ 3 ^ 20 < 4 * 2 ^ 30) ∧
    (4 * 2 ^ 31 ≤ 3 ^ 21 ∧ 3 ^ 21 < 5 * 2 ^ 31) ∧
    (7 * 2 ^ 32 ≤ 3 ^ 22 ∧ 3 ^ 22 < 8 * 2 ^ 32) ∧
    (10 * 2 ^ 33 ≤ 3 ^ 23 ∧ 3 ^ 23 < 11 * 2 ^ 33) := by norm_num


/-! Deprecated names retained for existing consumers; each is only an exponent comparison. -/

/-- Deprecated name for `post_l_odd_run_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias odd_run_never_drops := post_l_odd_run_exponent_not_lt

/-- Deprecated name for `post_l_ooe_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias post_l_ooe_no_drop := post_l_ooe_exponent_not_lt

/-- Deprecated name for `post_l_second_l_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias post_l_second_l_no_drop := post_l_second_l_exponent_not_lt

/-- Deprecated name for `m_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias m_no_contract := m_exponent_not_lt

/-- Deprecated name for `m_ooe_oe_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias m_ooe_oe_no_contract := m_ooe_oe_exponent_not_lt

/-- Deprecated name for `w5_even_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias w5_even_no_progress := w5_even_exponent_not_lt

/-- Deprecated name for `y_even_exponent_not_lt`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias y_even_no_progress := y_even_exponent_not_lt

/-- Deprecated name for `z_even_exponent_not_lt_two`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias z_even_not_sq := z_even_exponent_not_lt_two

/-- Deprecated name for `v_even_exponent_not_lt_four`; it does not assert non-descent of an orbit. -/
@[deprecated (since := "2026-09-24")]
alias v_even_not_fourth := v_even_exponent_not_lt_four

end Problems.Juggler.CycleMinEnvelopes
