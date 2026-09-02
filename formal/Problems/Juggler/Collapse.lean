import Problems.Juggler.Preimages

namespace Problems.Juggler

/-!
# Even-run residual evaluation

The fixed-itinerary threshold depends on `v`. A uniform-in-`ε` upgrade is
false: an even tower can collapse a huge perfect power of two onto `1`,
after which any odd tail stays at `1`. Formal exponent `α_v` is then
irrelevant. This is not a lower-envelope theory and does not replace
`eventually_no_first_even_contraction`.
-/

def alphaMargin (v : List Branch) : ℕ :=
  3 ^ oddCount v - 2 ^ (v.length + 1)

theorem minimal_superquadratic_margin {v : List Branch}
    (hα : 2 ^ (v.length + 1) < 3 ^ oddCount v) :
    1 ≤ alphaMargin v :=
  superquadratic_gap hα

theorem follows_replicate_odd_one : ∀ o, follows 1 (List.replicate o Branch.odd)
  | 0 => by simp [follows]
  | o + 1 => by
      rw [List.replicate_succ]
      refine ⟨rfl, ?_⟩
      simpa [floorPower_one] using follows_replicate_odd_one o

theorem image_replicate_odd_one : ∀ o, image 1 (List.replicate o Branch.odd) = 1
  | 0 => by simp
  | o + 1 => by
      rw [List.replicate_succ]
      simpa [floorPower_one] using image_replicate_odd_one o

theorem replicate_append_singleton (n : ℕ) (a : Branch) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  simpa using List.replicate_add n 1 a

theorem even_tower_to_one {k : ℕ} (hk : 1 ≤ k) :
    follows (2 ^ (2 ^ (k - 1))) (List.replicate k Branch.even) ∧
      image (2 ^ (2 ^ (k - 1))) (List.replicate k Branch.even) = 1 := by
  cases k with
  | zero => omega
  | succ m =>
      have hrep : List.replicate (m + 1) Branch.even =
          List.replicate m Branch.even ++ [Branch.even] :=
        replicate_append_singleton m .even
      have hu : follows (2 ^ (2 ^ m)) (List.replicate m Branch.even) :=
        follows_replicate_even_pow_two (by decide : (2 : ℕ) % 2 = 0) m
      have himg :
          image (2 ^ (2 ^ m)) (List.replicate m Branch.even) = 2 := by
        simpa [image_eq_iterate, List.length_replicate] using
          floorPower_iterate_even_pow_two_eq
            (a := 2) (k := m) (by decide : (2 : ℕ) % 2 = 0)
      have hv : follows 2 [Branch.even] := by
        change 2 % 2 = 0 ∧ follows (floorPower 2) []
        rw [floorPower_two]
        exact ⟨rfl, trivial⟩
      have himg2 : image 2 [Branch.even] = 1 := by
        simp [image, floorPower_two]
      refine ⟨?_, ?_⟩
      · simpa [hrep] using follows_append hu (by simpa [himg] using hv)
      · simpa [hrep, image_append, himg] using himg2

/-- An even tower can collapse `2^{2^{k-1}}` onto `1`. Any odd tail then
stays at `1`, so the first-even cell contracts. -/
theorem even_tower_odd_tail_contracts {k o : ℕ} (hk : 1 ≤ k) :
    follows (2 ^ (2 ^ (k - 1)))
        (List.replicate k Branch.even ++ List.replicate o Branch.odd) ∧
      image (2 ^ (2 ^ (k - 1)))
          (List.replicate k Branch.even ++ List.replicate o Branch.odd) = 1 ∧
        image (2 ^ (2 ^ (k - 1)))
            (List.replicate k Branch.even ++ List.replicate o Branch.odd) + 1 <
          (2 ^ (2 ^ (k - 1)) + 1) ^ 2 := by
  obtain ⟨hE, himgE⟩ := even_tower_to_one hk
  have hO := follows_replicate_odd_one o
  have himgO := image_replicate_odd_one o
  have hq : 2 ≤ 2 ^ (2 ^ (k - 1)) :=
    Nat.le_self_pow (pow_ne_zero (k - 1) (by decide : (2 : ℕ) ≠ 0)) 2
  refine ⟨follows_append hE (by simpa [himgE] using hO), ?_, ?_⟩
  · rw [image_append, himgE, himgO]
  · rw [image_append, himgE, himgO]
    have h9 : (2 + 1) ^ 2 ≤ (2 ^ (2 ^ (k - 1)) + 1) ^ 2 :=
      Nat.pow_le_pow_left (Nat.succ_le_succ hq) 2
    exact lt_of_lt_of_le (by decide : (1 : ℕ) + 1 < (2 + 1) ^ 2) h9

theorem three_k_superquadratic {k : ℕ} (hk : 2 ≤ k) :
    2 ^ (4 * k + 1) < 3 ^ (3 * k) := by
  have hk' : k = k - 2 + 2 := (Nat.sub_add_cancel hk).symm
  rw [hk']
  induction k - 2 with
  | zero => native_decide
  | succ m ih =>
      have hL : 2 ^ (4 * (m + 1 + 2) + 1) = 16 * 2 ^ (4 * (m + 2) + 1) := by
        have : 4 * (m + 1 + 2) + 1 = 4 + (4 * (m + 2) + 1) := by ring
        rw [this, Nat.pow_add]
      have hR : 3 ^ (3 * (m + 1 + 2)) = 27 * 3 ^ (3 * (m + 2)) := by
        have : 3 * (m + 1 + 2) = 3 + 3 * (m + 2) := by ring
        rw [this, Nat.pow_add]
      rw [hL, hR]
      have hlt : 16 * 2 ^ (4 * (m + 2) + 1) < 16 * 3 ^ (3 * (m + 2)) :=
        Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 16)
      have hle : 16 * 3 ^ (3 * (m + 2)) ≤ 27 * 3 ^ (3 * (m + 2)) :=
        Nat.mul_le_mul_right _ (by decide : 16 ≤ 27)
      exact lt_of_lt_of_le hlt hle

theorem even_tower_three_k_superquadratic {k : ℕ} (hk : 2 ≤ k) :
    2 ^ ((List.replicate k Branch.even ++
            List.replicate (3 * k) Branch.odd).length + 1) <
      3 ^ oddCount
        (List.replicate k Branch.even ++ List.replicate (3 * k) Branch.odd) := by
  simp [oddCount_append, oddCount_replicate_even, oddCount_replicate_odd,
    List.length_append, List.length_replicate]
  have hlen : k + 3 * k + 1 = 4 * k + 1 := by ring
  rw [hlen]
  exact three_k_superquadratic hk

theorem nat_le_two_pow : ∀ n, n ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
      have ih := nat_le_two_pow n
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
        rw [pow_succ, mul_comm]
      rw [hpow]
      have h1 : n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
      have hp : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) n)
      have h2 : 2 ^ n + 1 ≤ 2 * 2 ^ n := by omega
      exact le_trans h1 h2

/-- No threshold depending only on a uniform superquadratic margin can
rule out arbitrarily large first-even contraction cells. The family
`v_k = E^k O^{3k}` is formally expanding and collapses
`q_k = 2^{2^{k-1}}` onto `1`. -/
theorem changing_suffix_unbounded_contraction (N : ℕ) :
    ∃ k o q v,
      N ≤ q ∧
        2 ^ (v.length + 1) < 3 ^ oddCount v ∧
          v = List.replicate k Branch.even ++ List.replicate o Branch.odd ∧
            follows q v ∧ image q v + 1 < (q + 1) ^ 2 := by
  let k := N + 2
  let o := 3 * k
  let q := 2 ^ (2 ^ (k - 1))
  let v := List.replicate k Branch.even ++ List.replicate o Branch.odd
  refine ⟨k, o, q, v, ?_, ?_, rfl, ?_⟩
  · have h1 : N ≤ 2 ^ N := nat_le_two_pow N
    have h2 : N ≤ 2 ^ (N + 1) :=
      le_trans h1 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ N))
    have h3 : 2 ^ N ≤ 2 ^ (2 ^ (N + 1)) :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) h2
    have hk : k - 1 = N + 1 := by simp [k]
    simpa [q, hk] using le_trans h1 h3
  · simpa [v, o] using even_tower_three_k_superquadratic (k := k) (by simp [k])
  · have hk1 : 1 ≤ k := by simp [k]
    obtain ⟨hw, himg, hlt⟩ := even_tower_odd_tail_contracts (k := k) (o := o) hk1
    exact ⟨hw, by simpa [q, v, himg] using hlt⟩

/-!
## Collapse normalization

An initial even run is a scale change, not a new envelope. The residual
suffix sees `T_{E^r}(q)`, which on an exact even tower is the small
state `a`. This does not restore `Q(ε)`: an internal even run after an
odd letter can collapse in the same way. Not a halt theorem.
-/

def initialEvenRun : List Branch → ℕ
  | [] => 0
  | .even :: w => initialEvenRun w + 1
  | .odd :: _ => 0

def stripInitialEven : List Branch → List Branch
  | [] => []
  | .even :: w => stripInitialEven w
  | .odd :: w => .odd :: w

theorem initial_even_decomposition : ∀ v,
    v = List.replicate (initialEvenRun v) Branch.even ++ stripInitialEven v
  | [] => rfl
  | .odd :: _ => by simp [initialEvenRun, stripInitialEven]
  | .even :: w => by
      simp [initialEvenRun, stripInitialEven, List.replicate_succ]
      exact initial_even_decomposition w

theorem stripInitialEven_nil_or_odd :
    ∀ v, stripInitialEven v = [] ∨ ∃ u, stripInitialEven v = .odd :: u
  | [] => Or.inl rfl
  | .odd :: w => Or.inr ⟨w, rfl⟩
  | .even :: w => stripInitialEven_nil_or_odd w

theorem iterate_even_pow_two_eq {a k : ℕ} (ha : a % 2 = 0) :
    floorPower^[k] (a ^ (2 ^ k)) = a :=
  floorPower_iterate_even_pow_two_eq ha

theorem collapse_residual_identity (q r : ℕ) (u : List Branch) :
    image q (List.replicate r Branch.even ++ u) =
      image (image q (List.replicate r Branch.even)) u :=
  image_append q _ _

/-- Exact tower input: the suffix sees the compressed state `a`. -/
theorem collapse_on_pow_two {a r : ℕ} {u : List Branch}
    (ha : a % 2 = 0) (hu : follows a u) :
    follows (a ^ (2 ^ r)) (List.replicate r Branch.even ++ u) ∧
      image (a ^ (2 ^ r)) (List.replicate r Branch.even ++ u) = image a u := by
  have hE := follows_replicate_even_pow_two ha r
  have himg :
      image (a ^ (2 ^ r)) (List.replicate r Branch.even) = a := by
    simpa [image_eq_iterate, List.length_replicate] using
      iterate_even_pow_two_eq (a := a) (k := r) ha
  refine ⟨follows_append hE (by simpa [himg] using hu), ?_⟩
  rw [collapse_residual_identity, himg]

theorem collapse_tower_contracts_iff {a r : ℕ} {u : List Branch}
    (ha : a % 2 = 0) (hu : follows a u) :
    image (a ^ (2 ^ r)) (List.replicate r Branch.even ++ u) + 1 <
        (a ^ (2 ^ r) + 1) ^ 2 ↔
      image a u + 1 < (a ^ (2 ^ r) + 1) ^ 2 := by
  rw [(collapse_on_pow_two ha hu).2]

/-- The changing-suffix family is residual evaluation at `1`. -/
theorem even_tower_collapse_residual {k o : ℕ} (hk : 1 ≤ k) :
    image (2 ^ (2 ^ (k - 1)))
        (List.replicate k Branch.even ++ List.replicate o Branch.odd) =
      image 1 (List.replicate o Branch.odd) := by
  obtain ⟨_, himgE⟩ := even_tower_to_one hk
  rw [collapse_residual_identity, himgE]

theorem odd_then_even_collapse (q k : ℕ) (u : List Branch) :
    image q (.odd :: List.replicate k Branch.even ++ u) =
      image (image (floorPower q) (List.replicate k Branch.even)) u := by
  rw [List.cons_append, image_cons, collapse_residual_identity]

/-- `OEEE` followed by nine odds. Initial even-run length is `0`. -/
def itineraryOEEE9 : List Branch :=
  [.odd, .even, .even, .even, .odd, .odd, .odd, .odd, .odd, .odd, .odd, .odd, .odd]

theorem itineraryOEEE9_eq :
    itineraryOEEE9 =
      .odd :: List.replicate 3 Branch.even ++ List.replicate 9 Branch.odd :=
  rfl

theorem odd_even_tower_seven :
    follows 7 itineraryOEEE9 ∧ image 7 itineraryOEEE9 = 1 ∧
      image 7 itineraryOEEE9 + 1 < (7 + 1) ^ 2 := by
  have himg : image 7 itineraryOEEE9 = 1 := by
    simp [image, itineraryOEEE9, floorPower_seven, floorPower_eighteen,
      floorPower_four, floorPower_two, floorPower_one]
  have hw : follows 7 itineraryOEEE9 := by
    simp [follows, itineraryOEEE9, floorPower_seven, floorPower_eighteen,
      floorPower_four, floorPower_two, floorPower_one]
  exact ⟨hw, himg, by simp [himg]⟩

theorem odd_even_tower_seven_superquadratic :
    2 ^ (itineraryOEEE9.length + 1) < 3 ^ oddCount itineraryOEEE9 := by
  native_decide

/-!
## Internal even runs

A medial run `u E^r v` is residual evaluation at the exit state. The
inert basin is `1` under an odd tail. Syntactic `maxEvenRun ≤ R` does
not keep first-even contraction cells small: an extra even run before
`OEEE` lifts `q = 7` to `q = 2500`. Not a halt theorem.
-/

def maxEvenRunFrom (cur best : ℕ) : List Branch → ℕ
  | [] => max cur best
  | .even :: w => maxEvenRunFrom (cur + 1) best w
  | .odd :: w => maxEvenRunFrom 0 (max cur best) w

def maxEvenRun (w : List Branch) : ℕ := maxEvenRunFrom 0 0 w

theorem internal_even_collapse (q : ℕ) (u : List Branch) (r : ℕ)
    (v : List Branch) :
    image q (u ++ List.replicate r Branch.even ++ v) =
      image (image (image q u) (List.replicate r Branch.even)) v := by
  rw [image_append, image_append]

theorem collapse_basin_one (o : ℕ) :
    image 1 (List.replicate o Branch.odd) = 1 :=
  image_replicate_odd_one o

def itineraryEE_OEEE12 : List Branch :=
  [.even, .even] ++ itineraryOEEE9 ++ [.odd, .odd, .odd]

theorem floorPower_fifty : floorPower 50 = 7 := by
  native_decide

theorem floorPower_2500 : floorPower 2500 = 50 := by
  native_decide

theorem maxEvenRun_itineraryEE_OEEE12 : maxEvenRun itineraryEE_OEEE12 = 3 := by
  native_decide

theorem nested_even_collapse_2500 :
    follows 2500 itineraryEE_OEEE12 ∧ image 2500 itineraryEE_OEEE12 = 1 ∧
      image 2500 itineraryEE_OEEE12 + 1 < (2500 + 1) ^ 2 := by
  have himg : image 2500 itineraryEE_OEEE12 = 1 := by
    simp [itineraryEE_OEEE12, image, itineraryOEEE9, floorPower_2500, floorPower_fifty,
      floorPower_seven, floorPower_eighteen, floorPower_four, floorPower_two,
      floorPower_one]
  have hw : follows 2500 itineraryEE_OEEE12 := by
    simp [itineraryEE_OEEE12, follows, itineraryOEEE9, floorPower_2500, floorPower_fifty,
      floorPower_seven, floorPower_eighteen, floorPower_four, floorPower_two,
      floorPower_one]
  exact ⟨hw, himg, by simp [himg]⟩

theorem nested_even_collapse_2500_superquadratic :
    2 ^ (itineraryEE_OEEE12.length + 1) < 3 ^ oddCount itineraryEE_OEEE12 := by
  native_decide

end Problems.Juggler
