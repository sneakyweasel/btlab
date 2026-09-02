import Mathlib.Data.Nat.Factorization.Basic
import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

/-!
# Finite-itinerary envelope

One-sided floor-power composition on realized finite itineraries.
`EnvelopeState n x` is the free-exponent form `x^A ≤ n^B`.
Composition is `EnvelopeState.even` / `.odd` / `.map_itinerary`.
`PowerBound` is the itinerary-stat specialization `A = 2^k`, `B = 3^o`.
`power_bound_lt_pow` is `EnvelopeState.of_follows.lt_pow`.
`power_bound_contracts` is the `k = 1` case.
`power_bound_word` remains a public alias; new proofs should
prefer `EnvelopeState.of_follows`.
-/
/-- Named expansion of the OOOEE envelope `n5 ^ 32 ≤ n ^ 27`. -/
theorem floorPower_oooee_pow_chain
    {n n1 n2 n3 n4 n5 : ℕ}
    (h1 : n1 ^ 2 ≤ n ^ 3)
    (h2 : n2 ^ 2 ≤ n1 ^ 3)
    (h3 : n3 ^ 2 ≤ n2 ^ 3)
    (h4 : n4 ^ 2 ≤ n3)
    (h5 : n5 ^ 2 ≤ n4) :
    n5 ^ 32 ≤ n ^ 27 := by
  have h32 : n5 ^ 32 = (n5 ^ 2) ^ 16 := by
    calc
      n5 ^ 32 = n5 ^ (2 * 16) := by norm_num
      _ = (n5 ^ 2) ^ 16 := Nat.pow_mul n5 2 16
  have h16 : n4 ^ 16 = (n4 ^ 2) ^ 8 := by
    calc
      n4 ^ 16 = n4 ^ (2 * 8) := by norm_num
      _ = (n4 ^ 2) ^ 8 := Nat.pow_mul n4 2 8
  have h8 : n3 ^ 8 = (n3 ^ 2) ^ 4 := by
    calc
      n3 ^ 8 = n3 ^ (2 * 4) := by norm_num
      _ = (n3 ^ 2) ^ 4 := Nat.pow_mul n3 2 4
  have h12 : (n2 ^ 3) ^ 4 = n2 ^ 12 := by
    calc
      (n2 ^ 3) ^ 4 = n2 ^ (3 * 4) := (Nat.pow_mul n2 3 4).symm
      _ = n2 ^ 12 := by norm_num
  have h12' : n2 ^ 12 = (n2 ^ 2) ^ 6 := by
    calc
      n2 ^ 12 = n2 ^ (2 * 6) := by norm_num
      _ = (n2 ^ 2) ^ 6 := Nat.pow_mul n2 2 6
  have h18 : (n1 ^ 3) ^ 6 = n1 ^ 18 := by
    calc
      (n1 ^ 3) ^ 6 = n1 ^ (3 * 6) := (Nat.pow_mul n1 3 6).symm
      _ = n1 ^ 18 := by norm_num
  have h18' : n1 ^ 18 = (n1 ^ 2) ^ 9 := by
    calc
      n1 ^ 18 = n1 ^ (2 * 9) := by norm_num
      _ = (n1 ^ 2) ^ 9 := Nat.pow_mul n1 2 9
  have h27 : (n ^ 3) ^ 9 = n ^ 27 := by
    calc
      (n ^ 3) ^ 9 = n ^ (3 * 9) := (Nat.pow_mul n 3 9).symm
      _ = n ^ 27 := by norm_num
  calc
    n5 ^ 32 = (n5 ^ 2) ^ 16 := h32
    _ ≤ n4 ^ 16 := Nat.pow_le_pow_left h5 16
    _ = (n4 ^ 2) ^ 8 := h16
    _ ≤ n3 ^ 8 := Nat.pow_le_pow_left h4 8
    _ = (n3 ^ 2) ^ 4 := h8
    _ ≤ (n2 ^ 3) ^ 4 := Nat.pow_le_pow_left h3 4
    _ = n2 ^ 12 := h12
    _ = (n2 ^ 2) ^ 6 := h12'
    _ ≤ (n1 ^ 3) ^ 6 := Nat.pow_le_pow_left h2 6
    _ = n1 ^ 18 := h18
    _ = (n1 ^ 2) ^ 9 := h18'
    _ ≤ (n ^ 3) ^ 9 := Nat.pow_le_pow_left h1 9
    _ = n ^ 27 := h27

/-- Even-step composition of a square upper bound. -/
theorem pow_sq_le {a b e : ℕ} (h : a ^ 2 ≤ b) :
    a ^ (2 * e) ≤ b ^ e := by
  calc
    a ^ (2 * e) = (a ^ 2) ^ e := Nat.pow_mul a 2 e
    _ ≤ b ^ e := Nat.pow_le_pow_left h e

/-- Odd-step composition of a square-vs-cube upper bound. -/
theorem pow_sq_le_cube {a b e : ℕ} (h : a ^ 2 ≤ b ^ 3) :
    a ^ (2 * e) ≤ b ^ (3 * e) := by
  calc
    a ^ (2 * e) = (a ^ 2) ^ e := Nat.pow_mul a 2 e
    _ ≤ (b ^ 3) ^ e := Nat.pow_le_pow_left h e
    _ = b ^ (3 * e) := (Nat.pow_mul b 3 e).symm

/-- For `n ≥ 2`, a strictly larger exponent yields a strictly larger power. -/
theorem pow_lt_of_two_le {n a b : ℕ} (hn : 2 ≤ n) (hba : b < a) :
    n ^ b < n ^ a :=
  Nat.pow_lt_pow_right (lt_of_lt_of_le (by decide : 1 < 2) hn) hba

theorem two_pow_succ (k : ℕ) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [pow_succ, mul_comm]

theorem three_pow_succ (o : ℕ) : 3 ^ (o + 1) = 3 * 3 ^ o := by
  rw [pow_succ, mul_comm]

theorem pow_three_succ_right (n o : ℕ) :
    (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ (o + 1)) := by
  calc
    (n ^ (3 ^ o)) ^ 3 = n ^ (3 ^ o * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
    _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]
    _ = n ^ (3 ^ (o + 1)) := by rw [← pow_succ']

/-- Weak one-sided bound `m^{2^k} ≤ n^{3^o}`. Equality is allowed. -/
def PowerBound (m n k o : ℕ) : Prop := m ^ (2 ^ k) ≤ n ^ (3 ^ o)

theorem power_bound_empty (n : ℕ) : PowerBound n n 0 0 := by
  simp [PowerBound]

theorem power_bound_append_even {m n k o : ℕ}
    (h : PowerBound m n k o) (heven : m % 2 = 0) :
    PowerBound (floorPower m) n (k + 1) o := by
  have hsq : floorPower m ^ 2 ≤ m := floorPower_even_sq_le heven
  unfold PowerBound at *
  rw [two_pow_succ]
  exact le_trans (pow_sq_le hsq) h

theorem power_bound_append_odd {m n k o : ℕ}
    (h : PowerBound m n k o) (hodd : m % 2 = 1) :
    PowerBound (floorPower m) n (k + 1) (o + 1) := by
  have hsq : floorPower m ^ 2 ≤ m ^ 3 := floorPower_odd_sq_le_cube hodd
  unfold PowerBound at *
  rw [two_pow_succ, three_pow_succ]
  calc
    floorPower m ^ (2 * 2 ^ k) ≤ m ^ (3 * 2 ^ k) := pow_sq_le_cube hsq
    _ = (m ^ (2 ^ k)) ^ 3 := by rw [mul_comm, Nat.pow_mul]
    _ ≤ (n ^ (3 ^ o)) ^ 3 := Nat.pow_le_pow_left h 3
    _ = n ^ ((3 ^ o) * 3) := (Nat.pow_mul n (3 ^ o) 3).symm
    _ = n ^ (3 * 3 ^ o) := by rw [mul_comm]

theorem power_bound_from {start current k o : ℕ}
    (hbound : PowerBound current start k o) :
    ∀ w, follows current w →
      PowerBound (image current w) start (k + w.length)
        (o + oddCount w) := by
  intro w
  induction w generalizing current k o with
  | nil =>
      intro _
      simpa using hbound
  | cons b rest ih =>
      intro hw
      cases b with
      | even =>
          have heven : current % 2 = 0 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o)
              (power_bound_append_even hbound heven) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          simp [List.length_cons]
          rw [hk]
          exact hih
      | odd =>
          have hodd : current % 2 = 1 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hih :=
            ih (current := floorPower current) (k := k + 1) (o := o + 1)
              (power_bound_append_odd hbound hodd) hrest
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
          simp [List.length_cons]
          rw [hk, ho]
          exact hih

/-- Free-exponent envelope `x^A ≤ n^B`. `PowerBound` is the special
case `A = 2^k`, `B = 3^o`. Word algebra only. -/
structure EnvelopeState (n x : ℕ) where
  A : ℕ
  B : ℕ
  le : x ^ A ≤ n ^ B

/-- Even letter: `(A, B) → (2A, B)` from `T(x)^2 ≤ x`. -/
def EnvelopeState.even {n x : ℕ} (h : EnvelopeState n x) (heven : x % 2 = 0) :
    EnvelopeState n (floorPower x) where
  A := 2 * h.A
  B := h.B
  le := by
    have hsq : floorPower x ^ 2 ≤ x := floorPower_even_sq_le heven
    calc
      floorPower x ^ (2 * h.A) = (floorPower x ^ 2) ^ h.A := Nat.pow_mul _ 2 h.A
      _ ≤ x ^ h.A := Nat.pow_le_pow_left hsq h.A
      _ ≤ n ^ h.B := h.le

/-- Odd letter: `(A, B) → (2A, 3B)` from `T(x)^2 ≤ x^3`. -/
def EnvelopeState.odd {n x : ℕ} (h : EnvelopeState n x) (hodd : x % 2 = 1) :
    EnvelopeState n (floorPower x) where
  A := 2 * h.A
  B := 3 * h.B
  le := by
    have hsq : floorPower x ^ 2 ≤ x ^ 3 := floorPower_odd_sq_le_cube hodd
    calc
      floorPower x ^ (2 * h.A)
          = (floorPower x ^ 2) ^ h.A := Nat.pow_mul _ 2 h.A
      _ ≤ (x ^ 3) ^ h.A := Nat.pow_le_pow_left hsq h.A
      _ = x ^ (3 * h.A) := (Nat.pow_mul x 3 h.A).symm
      _ = (x ^ h.A) ^ 3 := by rw [Nat.mul_comm, Nat.pow_mul]
      _ ≤ (n ^ h.B) ^ 3 := Nat.pow_le_pow_left h.le 3
      _ = n ^ (h.B * 3) := (Nat.pow_mul n h.B 3).symm
      _ = n ^ (3 * h.B) := by rw [Nat.mul_comm]

/-- Empty-itinerary envelope: `n^1 ≤ n^1`. -/
def EnvelopeState.refl (n : ℕ) : EnvelopeState n n where
  A := 1
  B := 1
  le := by simp

/-- One realized letter. -/
def EnvelopeState.map_letter {n x : ℕ} (h : EnvelopeState n x) {b : Branch}
    (hw : follows x [b]) : EnvelopeState n (floorPower x) :=
  match b with
  | .even => h.even hw.1
  | .odd => h.odd hw.1

/-- Compose an envelope along a realized itinerary. -/
def EnvelopeState.map_itinerary {n x : ℕ} (h : EnvelopeState n x) :
    ∀ {w : List Branch}, follows x w → EnvelopeState n (image x w)
  | [], _ => by simpa [image] using h
  | .even :: rest, hw => (h.even hw.1).map_itinerary hw.2
  | .odd :: rest, hw => (h.odd hw.1).map_itinerary hw.2

theorem EnvelopeState.map_itinerary_A {n x : ℕ} (h : EnvelopeState n x) :
    ∀ {w : List Branch} (hw : follows x w),
      (h.map_itinerary hw).A = h.A * 2 ^ w.length
  | [], _ => by simp [EnvelopeState.map_itinerary]
  | .even :: rest, hw => by
      have ih := EnvelopeState.map_itinerary_A (h.even hw.1) hw.2
      simp [EnvelopeState.map_itinerary] at ih ⊢
      rw [ih, EnvelopeState.even]
      ring
  | .odd :: rest, hw => by
      have ih := EnvelopeState.map_itinerary_A (h.odd hw.1) hw.2
      simp [EnvelopeState.map_itinerary] at ih ⊢
      rw [ih, EnvelopeState.odd]
      ring

theorem EnvelopeState.map_itinerary_B {n x : ℕ} (h : EnvelopeState n x) :
    ∀ {w : List Branch} (hw : follows x w),
      (h.map_itinerary hw).B = h.B * 3 ^ oddCount w
  | [], _ => by simp [EnvelopeState.map_itinerary]
  | .even :: rest, hw => by
      have ih := EnvelopeState.map_itinerary_B (h.even hw.1) hw.2
      simp [EnvelopeState.map_itinerary] at ih ⊢
      rw [ih, EnvelopeState.even]
  | .odd :: rest, hw => by
      have ih := EnvelopeState.map_itinerary_B (h.odd hw.1) hw.2
      simp [EnvelopeState.map_itinerary] at ih ⊢
      rw [ih, EnvelopeState.odd]
      ring

def EnvelopeState.of_powerBound {m n k o : ℕ} (h : PowerBound m n k o) :
    EnvelopeState n m :=
  ⟨2 ^ k, 3 ^ o, h⟩

/-- Word envelope from `map_itinerary` on `refl`. -/
def EnvelopeState.of_follows {n : ℕ} {w : List Branch} (hw : follows n w) :
    EnvelopeState n (image n w) :=
  (EnvelopeState.refl n).map_itinerary hw

theorem EnvelopeState.of_follows_A {n : ℕ} {w : List Branch} (hw : follows n w) :
    (EnvelopeState.of_follows hw).A = 2 ^ w.length := by
  simp [EnvelopeState.of_follows, EnvelopeState.map_itinerary_A, EnvelopeState.refl]

theorem EnvelopeState.of_follows_B {n : ℕ} {w : List Branch} (hw : follows n w) :
    (EnvelopeState.of_follows hw).B = 3 ^ oddCount w := by
  simp [EnvelopeState.of_follows, EnvelopeState.map_itinerary_B, EnvelopeState.refl]

/-- Weak composition: every realized finite itinerary obeys the one-sided bound. -/
theorem power_bound_follows {n : ℕ} {w : List Branch} (hw : follows n w) :
    PowerBound (floorPower^[w.length] n) n w.length (oddCount w) := by
  have hle := (EnvelopeState.of_follows hw).le
  rw [EnvelopeState.of_follows_A hw, EnvelopeState.of_follows_B hw] at hle
  simpa [PowerBound, image_eq_iterate] using hle

/-- Unfolded form of `power_bound_follows`. Naming alias only. -/
theorem power_bound_word {n : ℕ} {w : List Branch} (hw : follows n w) :
    (floorPower^[w.length] n) ^ (2 ^ w.length) ≤ n ^ (3 ^ oddCount w) :=
  power_bound_follows hw

/-- Repeated realized `OE` blocks: `T^{2r}(x)^{4^r} ≤ x^{3^r}`. -/
theorem repeated_oe_scale {x r : ℕ} (hw : follows x (repeatedOE r)) :
    (floorPower^[2 * r] x) ^ (4 ^ r) ≤ x ^ (3 ^ r) := by
  have h := power_bound_word hw
  rw [length_repeatedOE, oddCount_repeatedOE] at h
  rw [← four_pow_eq_two_pow_two_mul] at h
  exact h

/-- Cell comparison: `x^A ≤ n^B` and `B < k·A` force `x < n^k`. -/
theorem envelope_lt_pow {x n A B k : ℕ}
    (hn : 2 ≤ n) (_hA : 0 < A) (h : x ^ A ≤ n ^ B) (hgap : B < k * A) :
    x < n ^ k := by
  refine Nat.lt_of_not_ge fun hge => ?_
  have hleft : n ^ (k * A) ≤ x ^ A := by
    calc
      n ^ (k * A) = (n ^ k) ^ A := Nat.pow_mul n k A
      _ ≤ x ^ A := Nat.pow_le_pow_left hge A
  have hle : n ^ (k * A) ≤ n ^ B := le_trans hleft h
  have hlt : n ^ B < n ^ (k * A) := pow_lt_of_two_le hn hgap
  exact (not_le_of_gt hlt) hle

theorem EnvelopeState.lt_pow {n x : ℕ} (h : EnvelopeState n x) {k : ℕ}
    (hn : 2 ≤ n) (hA : 0 < h.A) (hgap : h.B < k * h.A) :
    x < n ^ k :=
  envelope_lt_pow hn hA h.le hgap

/-- Word-stat form: `3^{oddCount w} < k · 2^{|w|}` yields `T_w(n) < n^k`.
Implemented by `EnvelopeState.of_follows`. `power_bound_contracts`
is the `k = 1` case. -/
theorem power_bound_lt_pow {n : ℕ} {w : List Branch} {k : ℕ}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < k * 2 ^ w.length) :
    image n w < n ^ k :=
  (EnvelopeState.of_follows hw).lt_pow hn
    (by
      rw [EnvelopeState.of_follows_A hw]
      exact Nat.pow_pos (by decide : (0 : ℕ) < 2))
    (by
      rw [EnvelopeState.of_follows_A hw, EnvelopeState.of_follows_B hw]
      exact hgap)

/-- Strict block contraction from the exponent gap. Domain `n ≥ 2`.
The `k = 1` case of `power_bound_lt_pow`. Not a claim that every
trajectory meets a negative-drift word. -/
theorem power_bound_contracts {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (hgap : 3 ^ oddCount w < 2 ^ w.length) :
    floorPower^[w.length] n < n := by
  have hlt := power_bound_lt_pow (k := 1) hn hw (by simpa using hgap)
  simpa [image_eq_iterate] using hlt

def itineraryOOOEE : List Branch := [.odd, .odd, .odd, .even, .even]

def itineraryOOOEEEOO : List Branch :=
  [.odd, .odd, .odd, .even, .even, .even, .odd, .odd]

theorem follows_itineraryOOOEE_iff {n : ℕ} :
    follows n itineraryOOOEE ↔
      n % 2 = 1 ∧
      floorPower n % 2 = 1 ∧
      floorPower (floorPower n) % 2 = 1 ∧
      floorPower (floorPower (floorPower n)) % 2 = 0 ∧
      floorPower (floorPower (floorPower (floorPower n))) % 2 = 0 := by
  simp [follows, itineraryOOOEE]

theorem follows_itineraryOOOEEEOO_iff {n : ℕ} :
    follows n itineraryOOOEEEOO ↔
      n % 2 = 1 ∧
      floorPower n % 2 = 1 ∧
      floorPower (floorPower n) % 2 = 1 ∧
      floorPower (floorPower (floorPower n)) % 2 = 0 ∧
      floorPower (floorPower (floorPower (floorPower n))) % 2 = 0 ∧
      floorPower (floorPower (floorPower (floorPower (floorPower n)))) % 2 = 0 ∧
      floorPower (floorPower (floorPower (floorPower (floorPower
          (floorPower n))))) % 2 = 1 ∧
      floorPower (floorPower (floorPower (floorPower (floorPower
          (floorPower (floorPower n)))))) % 2 = 1 := by
  simp [follows, itineraryOOOEEEOO]

theorem floorPower_oooee_of_follows {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOOEE) :
    floorPower^[5] n < n := by
  have h := power_bound_contracts (w := itineraryOOOEE) hn hw
  have hgap : 3 ^ oddCount itineraryOOOEE < 2 ^ itineraryOOOEE.length := by
    simp [itineraryOOOEE]
  simpa [itineraryOOOEE] using h hgap

theorem floorPower_oooeeeoo_of_follows {n : ℕ} (hn : 2 ≤ n)
    (hw : follows n itineraryOOOEEEOO) :
    floorPower^[8] n < n := by
  have h := power_bound_contracts (w := itineraryOOOEEEOO) hn hw
  have hgap : 3 ^ oddCount itineraryOOOEEEOO < 2 ^ itineraryOOOEEEOO.length := by
    simp [itineraryOOOEEEOO]
  simpa [itineraryOOOEEEOO] using h hgap

/-- On the OOOEE branch itinerary, `T^5(n) < n` for `n ≥ 2`. Wrapper of
`floorPower_oooee_of_follows`. Not a halt theorem. -/
theorem floorPower_oooee_five_step_lt
    {n : ℕ} (hn : 2 ≤ n) (h0 : n % 2 = 1)
    (h1 : floorPower n % 2 = 1)
    (h2 : floorPower (floorPower n) % 2 = 1)
    (h3 : floorPower (floorPower (floorPower n)) % 2 = 0)
    (h4 : floorPower (floorPower (floorPower (floorPower n))) % 2 = 0) :
    floorPower (floorPower (floorPower (floorPower (floorPower n)))) < n := by
  have hw : follows n itineraryOOOEE :=
    (follows_itineraryOOOEE_iff (n := n)).mpr ⟨h0, h1, h2, h3, h4⟩
  simpa [itineraryOOOEE] using floorPower_oooee_of_follows hn hw

/-- Power comparison for the OOOEEEOO floor-power block: five odd steps
and three even steps give `n8 ^ 256 ≤ n ^ 243`. Canonical exponents of
the itinerary exponent `243/256`. -/
theorem floorPower_oooeeeoo_pow_chain
    {n n1 n2 n3 n4 n5 n6 n7 n8 : ℕ}
    (h1 : n1 ^ 2 ≤ n ^ 3)
    (h2 : n2 ^ 2 ≤ n1 ^ 3)
    (h3 : n3 ^ 2 ≤ n2 ^ 3)
    (h4 : n4 ^ 2 ≤ n3)
    (h5 : n5 ^ 2 ≤ n4)
    (h6 : n6 ^ 2 ≤ n5)
    (h7 : n7 ^ 2 ≤ n6 ^ 3)
    (h8 : n8 ^ 2 ≤ n7 ^ 3) :
    n8 ^ 256 ≤ n ^ 243 := by
  calc
    n8 ^ 256 = n8 ^ (2 * 128) := by norm_num
    _ ≤ n7 ^ (3 * 128) := pow_sq_le_cube h8
    _ = n7 ^ 384 := by norm_num
    _ = n7 ^ (2 * 192) := by norm_num
    _ ≤ n6 ^ (3 * 192) := pow_sq_le_cube h7
    _ = n6 ^ 576 := by norm_num
    _ = n6 ^ (2 * 288) := by norm_num
    _ ≤ n5 ^ 288 := pow_sq_le h6
    _ = n5 ^ (2 * 144) := by norm_num
    _ ≤ n4 ^ 144 := pow_sq_le h5
    _ = n4 ^ (2 * 72) := by norm_num
    _ ≤ n3 ^ 72 := pow_sq_le h4
    _ = n3 ^ (2 * 36) := by norm_num
    _ ≤ n2 ^ (3 * 36) := pow_sq_le_cube h3
    _ = n2 ^ 108 := by norm_num
    _ = n2 ^ (2 * 54) := by norm_num
    _ ≤ n1 ^ (3 * 54) := pow_sq_le_cube h2
    _ = n1 ^ 162 := by norm_num
    _ = n1 ^ (2 * 81) := by norm_num
    _ ≤ n ^ (3 * 81) := pow_sq_le_cube h1
    _ = n ^ 243 := by norm_num

/-- On the OOOEEEOO branch itinerary, `T^8(n) < n` for `n ≥ 2`. Wrapper of
`floorPower_oooeeeoo_of_follows`. Not a halt theorem. -/
theorem floorPower_oooeeeoo_eight_step_lt
    {n : ℕ} (hn : 2 ≤ n) (h0 : n % 2 = 1)
    (h1 : floorPower n % 2 = 1)
    (h2 : floorPower (floorPower n) % 2 = 1)
    (h3 : floorPower (floorPower (floorPower n)) % 2 = 0)
    (h4 : floorPower (floorPower (floorPower (floorPower n))) % 2 = 0)
    (h5 : floorPower (floorPower (floorPower (floorPower (floorPower n)))) % 2 = 0)
    (h6 : floorPower (floorPower (floorPower (floorPower (floorPower
        (floorPower n))))) % 2 = 1)
    (h7 : floorPower (floorPower (floorPower (floorPower (floorPower
        (floorPower (floorPower n)))))) % 2 = 1) :
    floorPower (floorPower (floorPower (floorPower (floorPower (floorPower
        (floorPower (floorPower n))))))) < n := by
  have hw : follows n itineraryOOOEEEOO :=
    (follows_itineraryOOOEEEOO_iff (n := n)).mpr ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  simpa [itineraryOOOEEEOO] using floorPower_oooeeeoo_of_follows hn hw

/-- An all-even realized itinerary of length `k ≥ 1` contracts for `n ≥ 2`. -/
theorem even_itinerary_contracts {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hw : follows n (List.replicate k Branch.even)) :
    floorPower^[k] n < n := by
  have h := power_bound_contracts (w := List.replicate k Branch.even) hn hw
  have hgap :
      3 ^ oddCount (List.replicate k Branch.even) <
        2 ^ (List.replicate k Branch.even).length := by
    simp [oddCount_replicate_even, List.length_replicate]
    exact Nat.pos_iff_ne_zero.mp hk
  simpa [List.length_replicate] using h hgap

/-- Even-run envelope: `T^r(m)^{2^r} ≤ m`. No minimality. -/
theorem even_run_pow_le {m : ℕ} :
    ∀ {r : ℕ}, follows m (List.replicate r Branch.even) →
      (floorPower^[r] m) ^ (2 ^ r) ≤ m := by
  intro r
  induction r generalizing m with
  | zero =>
      intro _
      simp
  | succ r ih =>
      intro hw
      rw [List.replicate_succ] at hw
      have ih' := ih hw.2
      have hstep := floorPower_even_sq_le hw.1
      have hexp :
          (floorPower^[r] (floorPower m)) ^ (2 ^ (r + 1)) =
            ((floorPower^[r] (floorPower m)) ^ (2 ^ r)) ^ 2 := by
        have hr2 : 2 ^ (r + 1) = 2 ^ r * 2 := by
          rw [two_pow_succ, mul_comm]
        rw [hr2, Nat.pow_mul]
      rw [iterate_cons m r, hexp]
      exact le_trans (Nat.pow_le_pow_left ih' 2) hstep

theorem floorPower_iterate_odd_nondecreasing {m k : ℕ} (hm : 1 ≤ m)
    (hw : follows m (List.replicate k Branch.odd)) :
    m ≤ floorPower^[k] m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ] at hw
      have hodd : m % 2 = 1 := hw.1
      have hstep : m ≤ floorPower m := floorPower_odd_nondecreasing hm hodd
      have hrest := ih (le_trans hm hstep) hw.2
      rw [iterate_cons]
      exact le_trans hstep hrest

/-- An all-odd realized itinerary of length `k ≥ 1` expands for `n ≥ 3`. -/
theorem odd_itinerary_expands {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    (hw : follows n (List.replicate k Branch.odd)) :
    n < floorPower^[k] n := by
  cases k with
  | zero => exact (Nat.not_succ_le_zero 0 hk).elim
  | succ k =>
      rw [List.replicate_succ] at hw
      have hodd : n % 2 = 1 := hw.1
      have hgt : n < floorPower n := floorPower_odd_gt hn hodd
      have himgpos : 1 ≤ floorPower n := by omega
      have hrest : floorPower n ≤ floorPower^[k] (floorPower n) :=
        floorPower_iterate_odd_nondecreasing himgpos hw.2
      rw [iterate_cons]
      exact lt_of_lt_of_le hgt hrest

theorem two_pow_ne_three_pow {k o : ℕ} (hk : 1 ≤ k) : 2 ^ k ≠ 3 ^ o := by
  intro h
  have heven : 2 ^ k % 2 = 0 := by
    cases k with
    | zero => omega
    | succ k => simp [pow_succ]
  have hodd : ∀ t, 3 ^ t % 2 = 1 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => simp [pow_succ, Nat.mul_mod, ih]
  rw [h] at heven
  exact (by decide : ¬(1 : ℕ) = 0) ((hodd o).symm.trans heven)

/-- A realized return to `x ≥ 2` forces `2^r ≤ 3^o`. -/
theorem cycle_envelope {x : ℕ} {w : List Branch}
    (hx : 2 ≤ x) (hw : follows x w) (hret : image x w = x) :
    2 ^ w.length ≤ 3 ^ oddCount w := by
  have hpow := power_bound_word hw
  have himg : floorPower^[w.length] x = x := by
    rw [← image_eq_iterate, hret]
  rw [himg] at hpow
  exact (Nat.pow_le_pow_iff_right (show 1 < x by omega)).mp hpow

/-- Equality `2^r = 3^o` is impossible for a nonempty itinerary, so every
nontrivial cycle is strictly expanding in the exponent. -/
theorem cycle_strict_envelope {x : ℕ} {w : List Branch}
    (hx : 2 ≤ x) (hw : follows x w) (hret : image x w = x)
    (hlen : 1 ≤ w.length) :
    2 ^ w.length < 3 ^ oddCount w :=
  lt_of_le_of_ne (cycle_envelope hx hw hret) (two_pow_ne_three_pow hlen)

/-- Contracting words cannot close a cycle. -/
theorem cycle_not_contracting {x : ℕ} {w : List Branch}
    (hx : 2 ≤ x) (hw : follows x w) (hret : image x w = x) :
    ¬3 ^ oddCount w < 2 ^ w.length := by
  intro hgap
  have hlt := power_bound_contracts hx hw hgap
  have himg : floorPower^[w.length] x = x := by
    rw [← image_eq_iterate, hret]
  rw [himg] at hlt
  exact (lt_irrefl x) hlt

end Problems.Juggler
