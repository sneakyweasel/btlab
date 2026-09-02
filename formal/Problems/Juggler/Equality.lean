import Problems.Juggler.Envelope

namespace Problems.Juggler

/-!
# Envelope equality and saturation

Local branch equality, composite equality, and square rigidity.
Not a termination theorem, not an equality-itinerary classifier, and not a
`PowerBound` certificate datatype. `PowerBound` remains the weak bound.
-/

/-- Even branch: `T(n)^2 = n` iff `n` is a perfect square. -/
theorem floorPower_even_sq_eq_iff_square {n : ℕ} (heven : n % 2 = 0) :
    floorPower n ^ 2 = n ↔ n.sqrt ^ 2 = n := by
  rw [floorPower_even_eq heven]

lemma sqrt_sq_iff_isSquare (n : ℕ) : n.sqrt ^ 2 = n ↔ IsSquare n := by
  rw [isSquare_iff_exists_sq]
  constructor
  · intro h
    exact ⟨n.sqrt, h.symm⟩
  · rintro ⟨r, hr⟩
    simp [hr, Nat.sqrt_eq']

lemma isSquare_pow_three_iff {n : ℕ} : IsSquare (n ^ 3) ↔ IsSquare n := by
  simp_rw [isSquare_iff_exists_sq]
  constructor
  · rintro ⟨k, hk⟩
    rcases eq_or_ne n 0 with rfl | hn
    · exact ⟨0, by simp⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      have : n ^ 3 = 0 := by simpa using hk
      exact hn ((Nat.pow_eq_zero.mp this).1)
    set d := Nat.gcd k n
    have hd_dvd_k : d ∣ k := Nat.gcd_dvd_left k n
    have hd_dvd_n : d ∣ n := Nat.gcd_dvd_right k n
    obtain ⟨a, ha⟩ := hd_dvd_k
    obtain ⟨b, hb⟩ := hd_dvd_n
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_right k (Nat.pos_of_ne_zero hn)
    have hab : Nat.Coprime a b := by
      have hmul : Nat.gcd (d * a) (d * b) = d * Nat.gcd a b := Nat.gcd_mul_left d a b
      have : d * Nat.gcd a b = d := by
        rw [← hmul, ← ha, ← hb]
      have h1 : d * Nat.gcd a b = d * 1 := by
        rw [this, mul_one]
      exact Nat.mul_left_cancel hdpos h1
    have hpow : (d * a) ^ 2 = (d * b) ^ 3 := by
      rw [← ha, ← hb, hk]
    have hexp : d ^ 2 * a ^ 2 = d ^ 3 * b ^ 3 := by
      simpa [mul_pow] using hpow
    have hcancel : a ^ 2 = d * b ^ 3 := by
      have : d ^ 2 * a ^ 2 = d ^ 2 * (d * b ^ 3) := by
        have hre : d ^ 3 * b ^ 3 = d ^ 2 * (d * b ^ 3) := by ring
        rw [hexp, hre]
      exact Nat.mul_left_cancel (pow_pos hdpos 2) this
    have hb3 : b ^ 3 ∣ a ^ 2 := ⟨d, by rw [hcancel, mul_comm]⟩
    have hcop : Nat.Coprime (b ^ 3) (a ^ 2) := hab.symm.pow 3 2
    have hb1 : b = 1 := by
      have : b ^ 3 = 1 := hcop.eq_one_of_dvd hb3
      exact (Nat.pow_eq_one.mp this).resolve_right (by decide)
    refine ⟨a, ?_⟩
    rw [hb, hb1, mul_one, hcancel, hb1]
    ring
  · rintro ⟨s, hs⟩
    exact ⟨s ^ 3, by rw [hs]; ring⟩

lemma cube_sqrt_sq_iff (n : ℕ) :
    (n ^ 3).sqrt ^ 2 = n ^ 3 ↔ n.sqrt ^ 2 = n := by
  rw [sqrt_sq_iff_isSquare, sqrt_sq_iff_isSquare, isSquare_pow_three_iff]

/-- Odd branch: `T(n)^2 = n^3` iff `n` is a perfect square. -/
theorem floorPower_odd_sq_eq_cube_iff_square {n : ℕ} (hodd : n % 2 = 1) :
    floorPower n ^ 2 = n ^ 3 ↔ n.sqrt ^ 2 = n := by
  rw [floorPower_odd_eq hodd]
  exact cube_sqrt_sq_iff n

/-- Equality form of the one-sided envelope. Independent of `PowerBound`. -/
def PowerBoundEq (m n k o : ℕ) : Prop := m ^ (2 ^ k) = n ^ (3 ^ o)

theorem pow_eq_of_pow_sq_eq {a b e : ℕ} (he : e ≠ 0)
    (h : (a ^ 2) ^ e = b ^ e) : a ^ 2 = b :=
  Nat.pow_left_injective he h

theorem pow_ne_zero_two_pow (k : ℕ) : 2 ^ k ≠ 0 :=
  (Nat.pow_pos (by decide : (0 : ℕ) < 2)).ne'

/-- Even append: composite equality forces the previous equality and local tightness. -/
theorem power_bound_eq_of_append_even {m n k o : ℕ}
    (heven : m % 2 = 0) (hprev : PowerBound m n k o)
    (heq : PowerBoundEq (floorPower m) n (k + 1) o) :
    PowerBoundEq m n k o ∧ floorPower m ^ 2 = m := by
  have hlocal : floorPower m ^ 2 ≤ m := floorPower_even_sq_le heven
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hA : (floorPower m ^ 2) ^ (2 ^ k) ≤ m ^ (2 ^ k) :=
    Nat.pow_le_pow_left hlocal _
  have hA' : floorPower m ^ (2 ^ (k + 1)) ≤ m ^ (2 ^ k) := by
    rw [h2, Nat.pow_mul]
    exact hA
  have hB : m ^ (2 ^ k) ≤ n ^ (3 ^ o) := hprev
  have hends : floorPower m ^ (2 ^ (k + 1)) = n ^ (3 ^ o) := heq
  have hmid : floorPower m ^ (2 ^ (k + 1)) = m ^ (2 ^ k) :=
    le_antisymm hA' (hB.trans_eq hends.symm)
  have hprevEq : PowerBoundEq m n k o := le_antisymm hB (hends.symm.trans_le hA')
  refine ⟨hprevEq, ?_⟩
  have hpow : (floorPower m ^ 2) ^ (2 ^ k) = m ^ (2 ^ k) := by
    rw [← Nat.pow_mul, ← h2, hmid]
  have hk : 2 ^ k ≠ 0 := pow_ne_zero_two_pow k
  exact pow_eq_of_pow_sq_eq hk hpow

/-- Odd append: composite equality forces the previous equality and local tightness. -/
theorem power_bound_eq_of_append_odd {m n k o : ℕ}
    (hodd : m % 2 = 1) (hprev : PowerBound m n k o)
    (heq : PowerBoundEq (floorPower m) n (k + 1) (o + 1)) :
    PowerBoundEq m n k o ∧ floorPower m ^ 2 = m ^ 3 := by
  have hlocal : floorPower m ^ 2 ≤ m ^ 3 := floorPower_odd_sq_le_cube hodd
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have h3 : 3 ^ (o + 1) = 3 * 3 ^ o := three_pow_succ o
  have hA : (floorPower m ^ 2) ^ (2 ^ k) ≤ (m ^ 3) ^ (2 ^ k) :=
    Nat.pow_le_pow_left hlocal _
  have hA' : floorPower m ^ (2 ^ (k + 1)) ≤ m ^ (3 * 2 ^ k) := by
    rw [h2, Nat.pow_mul]
    simpa [Nat.pow_mul] using hA
  have hmid : m ^ (3 * 2 ^ k) = (m ^ (2 ^ k)) ^ 3 := by
    rw [mul_comm, Nat.pow_mul]
  have hB : (m ^ (2 ^ k)) ^ 3 ≤ (n ^ (3 ^ o)) ^ 3 :=
    Nat.pow_le_pow_left hprev 3
  have hB' : m ^ (3 * 2 ^ k) ≤ n ^ (3 ^ (o + 1)) := by
    rw [hmid, h3, mul_comm, Nat.pow_mul]
    exact hB
  have hends : floorPower m ^ (2 ^ (k + 1)) = n ^ (3 ^ (o + 1)) := heq
  have hchain1 : floorPower m ^ (2 ^ (k + 1)) = m ^ (3 * 2 ^ k) :=
    le_antisymm hA' (hB'.trans_eq hends.symm)
  have hchain2 : m ^ (3 * 2 ^ k) = n ^ (3 ^ (o + 1)) :=
    le_antisymm hB' (hends.symm.trans_le hA')
  have hprevEq : PowerBoundEq m n k o := by
    have : (m ^ (2 ^ k)) ^ 3 = (n ^ (3 ^ o)) ^ 3 := by
      rw [← hmid, hchain2, h3, mul_comm, Nat.pow_mul]
    exact Nat.pow_left_injective (by decide : (3 : ℕ) ≠ 0) this
  refine ⟨hprevEq, ?_⟩
  have hpow : (floorPower m ^ 2) ^ (2 ^ k) = (m ^ 3) ^ (2 ^ k) := by
    have : floorPower m ^ (2 * 2 ^ k) = m ^ (3 * 2 ^ k) := by
      simpa [h2] using hchain1
    simpa [Nat.pow_mul] using this
  have hk : 2 ^ k ≠ 0 := pow_ne_zero_two_pow k
  exact pow_eq_of_pow_sq_eq hk hpow

/-- Local tightness of one realized letter. -/
def localTight : ℕ → Branch → Prop
  | x, .even => floorPower x ^ 2 = x
  | x, .odd => floorPower x ^ 2 = x ^ 3

/-- Every local branch inequality along a realized itinerary is tight. -/
def localsTight (n : ℕ) : List Branch → Prop
  | [] => True
  | b :: w => localTight n b ∧ localsTight (floorPower n) w

theorem localTight_even_iff_square {n : ℕ} (heven : n % 2 = 0) :
    localTight n .even ↔ n.sqrt ^ 2 = n :=
  floorPower_even_sq_eq_iff_square heven

theorem localTight_odd_iff_square {n : ℕ} (hodd : n % 2 = 1) :
    localTight n .odd ↔ n.sqrt ^ 2 = n :=
  floorPower_odd_sq_eq_cube_iff_square hodd

theorem power_bound_eq_from {start current k o : ℕ} :
    ∀ w, PowerBound current start k o → follows current w →
      PowerBoundEq (image current w) start (k + w.length) (o + oddCount w) →
        PowerBoundEq current start k o ∧ localsTight current w := by
  intro w
  induction w generalizing current k o with
  | nil =>
      intro hbound _ heq
      exact ⟨heq, trivial⟩
  | cons b rest ih =>
      intro hbound hw heq
      cases b with
      | even =>
          have heven : current % 2 = 0 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hbound' : PowerBound (floorPower current) start (k + 1) o :=
            power_bound_append_even hbound heven
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have heq' :
              PowerBoundEq (image (floorPower current) rest) start
                (k + 1 + rest.length) (o + oddCount rest) := by
            simpa [List.length_cons, hk] using heq
          have hih := ih hbound' hrest heq'
          have hstep := power_bound_eq_of_append_even heven hbound hih.1
          exact ⟨hstep.1, ⟨hstep.2, hih.2⟩⟩
      | odd =>
          have hodd : current % 2 = 1 := hw.1
          have hrest : follows (floorPower current) rest := hw.2
          have hbound' : PowerBound (floorPower current) start (k + 1) (o + 1) :=
            power_bound_append_odd hbound hodd
          have hk : k + (rest.length + 1) = k + 1 + rest.length := by omega
          have ho : o + (oddCount rest + 1) = o + 1 + oddCount rest := by omega
          have heq' :
              PowerBoundEq (image (floorPower current) rest) start
                (k + 1 + rest.length) (o + 1 + oddCount rest) := by
            simpa [List.length_cons, hk, ho] using heq
          have hih := ih hbound' hrest heq'
          have hstep := power_bound_eq_of_append_odd hodd hbound hih.1
          exact ⟨hstep.1, ⟨hstep.2, hih.2⟩⟩

theorem localsTight_get {n : ℕ} :
    ∀ w, localsTight n w →
      ∀ i, (hi : i < w.length) →
        localTight (floorPower^[i] n) w[i] := by
  intro w
  induction w generalizing n with
  | nil =>
      intro _ i hi
      cases hi
  | cons b rest ih =>
      intro h i hi
      cases i with
      | zero =>
          simpa [localTight] using h.1
      | succ j =>
          have hj : j < rest.length := by
            simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
          have hget : (b :: rest)[j + 1] = rest[j] := rfl
          have hiter : floorPower^[j + 1] n = floorPower^[j] (floorPower n) :=
            iterate_cons n j
          simpa [hget, hiter] using ih h.2 j hj

/-- Global envelope equality forces every local branch inequality to be tight. -/
theorem power_bound_eq_implies_local_eq {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (heq : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) :
    ∀ i, (hi : i < w.length) → localTight (floorPower^[i] n) w[i] := by
  have h :=
    power_bound_eq_from (w := w) (power_bound_empty n) hw
      (by simpa [image_eq_iterate] using heq)
  exact localsTight_get w h.2


/-- Global envelope equality forces every relevant itinerary state to be a square. -/
theorem power_bound_eq_implies_square {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (heq : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) :
    ∀ i, i < w.length → (floorPower^[i] n).sqrt ^ 2 = floorPower^[i] n := by
  intro i hi
  have hloc := power_bound_eq_implies_local_eq hw heq i hi
  rcases hbranch : w[i] with _ | _
  · have heven := follows_get_even w hw i hi hbranch
    have : floorPower (floorPower^[i] n) ^ 2 = floorPower^[i] n := by
      simpa [localTight, hbranch] using hloc
    exact (floorPower_even_sq_eq_iff_square heven).mp this
  · have hodd := follows_get_odd w hw i hi hbranch
    have : floorPower (floorPower^[i] n) ^ 2 = (floorPower^[i] n) ^ 3 := by
      simpa [localTight, hbranch] using hloc
    exact (floorPower_odd_sq_eq_cube_iff_square hodd).mp this

/-- Even square: the even branch is exact as an image, not only as a power. -/
theorem floorPower_of_even_sq {s : ℕ} (heven : (s ^ 2) % 2 = 0) :
    floorPower (s ^ 2) = s := by
  have step : floorPower (s ^ 2) = (s ^ 2).sqrt := by simp [floorPower, heven]
  rw [step, Nat.sqrt_eq']

/-- Odd square: the odd branch maps `s^2` to `s^3`. -/
theorem floorPower_of_odd_sq {s : ℕ} (hodd : s % 2 = 1) :
    floorPower (s ^ 2) = s ^ 3 := by
  have hpow := floorPower_odd_sq_eq_cube_of_sq hodd
  have : floorPower (s ^ 2) ^ 2 = (s ^ 3) ^ 2 := by
    have hcube : (s ^ 2) ^ 3 = (s ^ 3) ^ 2 := by ring
    exact hpow.trans hcube
  exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) this

theorem floorPower_even_sq_image_even {s : ℕ} (heven : (s ^ 2) % 2 = 0) :
    floorPower (s ^ 2) % 2 = 0 := by
  rw [floorPower_of_even_sq heven]
  have : Even (s ^ 2) := Nat.even_iff.2 heven
  have hs : Even s := (Nat.even_pow' (by decide : (2 : ℕ) ≠ 0)).1 this
  exact Nat.even_iff.1 hs

theorem floorPower_odd_sq_image_odd {s : ℕ} (hodd : s % 2 = 1) :
    floorPower (s ^ 2) % 2 = 1 := by
  rw [floorPower_of_odd_sq hodd]
  have : (s ^ 3) % 2 = 1 := by
    have hodd0 : s % 2 ≠ 0 := by omega
    simp [Nat.pow_mod, hodd]
  exact this

/-!
2-adic perfect-power depth of equality-saturating states.
Not a reusable height abstraction and not a termination theorem.
`HasPowTwoDepth n r` means `n` is a `2^r`-th power.
-/

def HasPowTwoDepth (n r : ℕ) : Prop := ∃ a, n = a ^ (2 ^ r)

theorem hasPowTwoDepth_zero (n : ℕ) : HasPowTwoDepth n 0 :=
  ⟨n, by simp⟩

theorem two_pow_pred {r : ℕ} (hr : 1 ≤ r) : 2 ^ r = 2 * 2 ^ (r - 1) := by
  cases r with
  | zero => exact (Nat.not_succ_le_zero 0 hr).elim
  | succ r => rw [Nat.add_sub_cancel, Nat.pow_succ']

theorem pow_two_succ_sq (a r : ℕ) :
    a ^ (2 ^ (r + 1)) = (a ^ (2 ^ r)) ^ 2 := by
  rw [pow_succ (2 : ℕ), Nat.pow_mul]

theorem pow_two_pred_sq {a r : ℕ} (hr : 1 ≤ r) :
    a ^ (2 ^ r) = (a ^ (2 ^ (r - 1))) ^ 2 := by
  rw [two_pow_pred hr, mul_comm, Nat.pow_mul]

/-- Exact even branch on a `2^r`-th power, `r ≥ 1`. -/
theorem floorPower_of_pow_two_depth_even {a r : ℕ} (hr : 1 ≤ r)
    (heven : (a ^ (2 ^ r)) % 2 = 0) :
    floorPower (a ^ (2 ^ r)) = a ^ (2 ^ (r - 1)) := by
  have hrep := pow_two_pred_sq (a := a) hr
  rw [hrep] at heven ⊢
  exact floorPower_of_even_sq heven

theorem pow_mod_two_of_odd {a e : ℕ} (hodd : a % 2 = 1) :
    (a ^ e) % 2 = 1 := by
  simp [Nat.pow_mod, hodd]

theorem odd_of_pow_odd {a e : ℕ} (he : 1 ≤ e) (h : (a ^ e) % 2 = 1) :
    a % 2 = 1 := by
  by_contra hne
  have heven : a % 2 = 0 := by omega
  have : Even (a ^ e) := by
    rw [Nat.even_pow]
    exact ⟨Nat.even_iff.2 heven, Nat.pos_iff_ne_zero.mp he⟩
  have : (a ^ e) % 2 = 0 := Nat.even_iff.1 this
  omega

/-- Exact odd branch on a `2^r`-th power, `r ≥ 1`. -/
theorem floorPower_of_pow_two_depth_odd {a r : ℕ} (hr : 1 ≤ r)
    (hodd : a % 2 = 1) :
    floorPower (a ^ (2 ^ r)) = a ^ (3 * 2 ^ (r - 1)) := by
  have hs : (a ^ (2 ^ (r - 1))) % 2 = 1 := pow_mod_two_of_odd hodd
  have hrep := pow_two_pred_sq (a := a) hr
  rw [hrep]
  have himg : floorPower ((a ^ (2 ^ (r - 1))) ^ 2) = (a ^ (2 ^ (r - 1))) ^ 3 :=
    floorPower_of_odd_sq hs
  rw [himg, ← pow_mul, mul_comm]

theorem hasPowTwoDepth_sq {s r : ℕ} (h : HasPowTwoDepth s r) :
    HasPowTwoDepth (s ^ 2) (r + 1) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [ha, pow_two_succ_sq]

theorem hasPowTwoDepth_one_iff (n : ℕ) :
    HasPowTwoDepth n 1 ↔ n.sqrt ^ 2 = n := by
  constructor
  · rintro ⟨a, ha⟩
    have : n = a ^ 2 := by simpa using ha
    simp [this, Nat.sqrt_eq']
  · intro h
    exact ⟨n.sqrt, h.symm⟩

/-- A cube that is a `2^m`-th power is the cube of a `2^m`-th power's base. -/
theorem hasPowTwoDepth_of_cube {s m : ℕ}
    (h : HasPowTwoDepth (s ^ 3) m) : HasPowTwoDepth s m := by
  induction m generalizing s with
  | zero => exact ⟨s, by simp⟩
  | succ m ih =>
      obtain ⟨a, ha⟩ := h
      have hsq : IsSquare (s ^ 3) := by
        refine ⟨a ^ (2 ^ m), ?_⟩
        have : a ^ (2 ^ (m + 1)) = (a ^ (2 ^ m)) ^ 2 := pow_two_succ_sq a m
        rw [ha, this, pow_two]
      have hs : IsSquare s := (isSquare_pow_three_iff (n := s)).mp hsq
      obtain ⟨t, ht⟩ := (isSquare_iff_exists_sq s).1 hs
      have ht3 : t ^ 3 = a ^ (2 ^ m) := by
        have hpow : (t ^ 3) ^ 2 = (a ^ (2 ^ m)) ^ 2 := by
          calc
            (t ^ 3) ^ 2 = t ^ 6 := by ring
            _ = (t ^ 2) ^ 3 := by ring
            _ = s ^ 3 := by rw [ht]
            _ = a ^ (2 ^ (m + 1)) := ha
            _ = (a ^ (2 ^ m)) ^ 2 := pow_two_succ_sq a m
        exact Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hpow
      obtain ⟨b, hb⟩ := ih ⟨a, ht3⟩
      refine ⟨b, ?_⟩
      rw [ht, hb, pow_two_succ_sq]

/-- Even exact step drops 2-adic depth by one. -/
theorem hasPowTwoDepth_even_exact {n r : ℕ} (hr : 1 ≤ r)
    (h : HasPowTwoDepth n r) (heven : n % 2 = 0) :
    HasPowTwoDepth (floorPower n) (r - 1) := by
  obtain ⟨a, ha⟩ := h
  rw [ha, floorPower_of_pow_two_depth_even hr (by simpa [ha] using heven)]
  exact ⟨a, rfl⟩

/-- Odd exact step drops 2-adic depth by one (`a^{3·2^{r-1}} = (a^3)^{2^{r-1}}`). -/
theorem hasPowTwoDepth_odd_exact {n r : ℕ} (hr : 1 ≤ r)
    (h : HasPowTwoDepth n r) (hodd : n % 2 = 1) :
    HasPowTwoDepth (floorPower n) (r - 1) := by
  obtain ⟨a, ha⟩ := h
  have haodd : a % 2 = 1 :=
    odd_of_pow_odd (Nat.one_le_pow _ _ (by decide : 0 < 2)) (by simpa [ha] using hodd)
  rw [ha, floorPower_of_pow_two_depth_odd hr haodd]
  refine ⟨a ^ 3, ?_⟩
  rw [← pow_mul, mul_comm]

/-- Depth at least 2 forces the exact image to remain a square. -/
theorem hasPowTwoDepth_ge_two_image_square {n r : ℕ} (hr : 2 ≤ r)
    (h : HasPowTwoDepth n r) :
    (floorPower n).sqrt ^ 2 = floorPower n := by
  have hr1 : 1 ≤ r := le_trans (by decide : 1 ≤ 2) hr
  have himg : HasPowTwoDepth (floorPower n) (r - 1) := by
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · exact hasPowTwoDepth_even_exact hr1 h heven
    · exact hasPowTwoDepth_odd_exact hr1 h hodd
  have : 1 ≤ r - 1 := by omega
  have : HasPowTwoDepth (floorPower n) 1 := by
    obtain ⟨a, ha⟩ := himg
    refine ⟨a ^ (2 ^ (r - 1 - 1)), ?_⟩
    have hpow : 2 ^ (r - 1) = 2 * 2 ^ (r - 1 - 1) := two_pow_pred this
    have : floorPower n = (a ^ (2 ^ (r - 1 - 1))) ^ 2 := by
      rw [ha, hpow, mul_comm, Nat.pow_mul]
    simpa [HasPowTwoDepth, pow_one] using this
  exact (hasPowTwoDepth_one_iff _).1 this

/-- Depth exactly one: the exact image need not be a square. -/
theorem hasPowTwoDepth_one_image_sq_iff {a : ℕ}
    (heven : (a ^ 2) % 2 = 0) :
    (floorPower (a ^ 2)).sqrt ^ 2 = floorPower (a ^ 2) ↔ a.sqrt ^ 2 = a := by
  rw [floorPower_of_even_sq heven]

theorem hasPowTwoDepth_one_odd_image_sq_iff {a : ℕ} (hodd : a % 2 = 1) :
    (floorPower (a ^ 2)).sqrt ^ 2 = floorPower (a ^ 2) ↔ a.sqrt ^ 2 = a := by
  rw [floorPower_of_odd_sq hodd]
  exact cube_sqrt_sq_iff a

theorem localsTight_implies_power_bound_eq {n : ℕ} :
    ∀ w, follows n w → localsTight n w →
      PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w) := by
  intro w
  induction w generalizing n with
  | nil =>
      intro _ _
      simp [PowerBoundEq]
  | cons b rest ih =>
      intro hw hloc
      cases b with
      | even =>
          have heven : n % 2 = 0 := hw.1
          have hrest : follows (floorPower n) rest := hw.2
          have htail := ih hrest hloc.2
          have hlocal : floorPower n ^ 2 = n := by
            simpa [localTight] using hloc.1
          have hlen : (Branch.even :: rest).length = rest.length + 1 :=
            List.length_cons
          have ho : oddCount (Branch.even :: rest) = oddCount rest := rfl
          unfold PowerBoundEq at htail ⊢
          have h2 : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
            rw [pow_succ, mul_comm]
          rw [hlen, ho, iterate_cons, h2]
          calc
            (floorPower^[rest.length] (floorPower n)) ^ (2 * 2 ^ rest.length)
              = ((floorPower^[rest.length] (floorPower n)) ^ (2 ^ rest.length)) ^ 2 := by
                rw [mul_comm, Nat.pow_mul]
            _ = (floorPower n ^ (3 ^ oddCount rest)) ^ 2 := by rw [htail]
            _ = (floorPower n ^ 2) ^ (3 ^ oddCount rest) := by
              rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
            _ = n ^ (3 ^ oddCount rest) := by rw [hlocal]
      | odd =>
          have hodd : n % 2 = 1 := hw.1
          have hrest : follows (floorPower n) rest := hw.2
          have htail := ih hrest hloc.2
          have hlocal : floorPower n ^ 2 = n ^ 3 := by
            simpa [localTight] using hloc.1
          have hlen : (Branch.odd :: rest).length = rest.length + 1 :=
            List.length_cons
          have ho : oddCount (Branch.odd :: rest) = oddCount rest + 1 := rfl
          unfold PowerBoundEq at htail ⊢
          have h2 : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
            rw [pow_succ, mul_comm]
          rw [hlen, ho, iterate_cons, h2]
          have h3 : 3 ^ (oddCount rest + 1) = 3 * 3 ^ oddCount rest := by
            rw [pow_succ, mul_comm]
          rw [h3]
          calc
            (floorPower^[rest.length] (floorPower n)) ^ (2 * 2 ^ rest.length)
              = ((floorPower^[rest.length] (floorPower n)) ^ (2 ^ rest.length)) ^ 2 := by
                rw [mul_comm, Nat.pow_mul]
            _ = (floorPower n ^ (3 ^ oddCount rest)) ^ 2 := by rw [htail]
            _ = (floorPower n ^ 2) ^ (3 ^ oddCount rest) := by
              rw [← Nat.pow_mul, mul_comm, Nat.pow_mul]
            _ = (n ^ 3) ^ (3 ^ oddCount rest) := by rw [hlocal]
            _ = n ^ (3 * 3 ^ oddCount rest) := (Nat.pow_mul n 3 _).symm

/-- Envelope equality of length `k` forces the start to be a `2^k`-th power. -/
theorem power_bound_eq_implies_pow_two_depth {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (heq : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) :
    HasPowTwoDepth n w.length := by
  induction w generalizing n with
  | nil => exact hasPowTwoDepth_zero n
  | cons b rest ih =>
      have hfrom :=
        power_bound_eq_from (w := b :: rest) (power_bound_empty n) hw
          (by simpa [image_eq_iterate] using heq)
      have hloc : localsTight n (b :: rest) := hfrom.2
      have hsq : n.sqrt ^ 2 = n :=
        power_bound_eq_implies_square hw heq 0 (Nat.succ_pos _)
      set s := n.sqrt
      have hn : n = s ^ 2 := hsq.symm
      have hrest : follows (floorPower n) rest := by
        cases b with
        | even => exact hw.2
        | odd => exact hw.2
      have htailEq :
          PowerBoundEq (floorPower^[rest.length] (floorPower n)) (floorPower n)
            rest.length (oddCount rest) :=
        localsTight_implies_power_bound_eq rest hrest hloc.2
      have hdepth : HasPowTwoDepth (floorPower n) rest.length :=
        ih hrest htailEq
      have hr : 1 ≤ (b :: rest).length := Nat.succ_pos _
      cases b with
      | even =>
          have heven : n % 2 = 0 := hw.1
          have himg : floorPower n = s := by
            have : floorPower (s ^ 2) = s := floorPower_of_even_sq (by simpa [hn] using heven)
            simpa [hn] using this
          have : HasPowTwoDepth s rest.length := by simpa [himg] using hdepth
          simpa [hn, List.length_cons] using hasPowTwoDepth_sq this
      | odd =>
          have hodd : n % 2 = 1 := hw.1
          have hsodd : s % 2 = 1 :=
            odd_of_pow_odd (by decide : 1 ≤ 2) (by simpa [hn] using hodd)
          have himg : floorPower n = s ^ 3 := by
            have : floorPower (s ^ 2) = s ^ 3 := floorPower_of_odd_sq hsodd
            simpa [hn] using this
          have : HasPowTwoDepth (s ^ 3) rest.length := by simpa [himg] using hdepth
          have hs : HasPowTwoDepth s rest.length := hasPowTwoDepth_of_cube this
          simpa [hn, List.length_cons] using hasPowTwoDepth_sq hs

theorem hasPowTwoDepth_two_le {n r : ℕ} (hn : 2 ≤ n) (h : HasPowTwoDepth n r) :
    2 ^ (2 ^ r) ≤ n := by
  obtain ⟨a, ha⟩ := h
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : a ≤ 1 := Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
    interval_cases a
    · have : n = 0 := by simp [ha]
      omega
    · have : n = 1 := by simp [ha]
      omega
  have : 2 ^ (2 ^ r) ≤ a ^ (2 ^ r) := Nat.pow_le_pow_left ha2 _
  simpa [ha] using this

/-- A contracting equality itinerary of length `k` at `n ≥ 2` is at least `2^{2^k}`. -/
theorem power_bound_eq_contracts_pow_two_lb {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (hw : follows n w)
    (heq : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) :
    2 ^ (2 ^ w.length) ≤ n :=
  hasPowTwoDepth_two_le hn (power_bound_eq_implies_pow_two_depth hw heq)

/-!
## Extremal equality language

Parity rigidity of exact perfect-power states, and the monochrome
equality-itinerary language. Not an equality-itinerary census and not a
termination theorem.
-/

theorem even_iff_pow_even {a e : ℕ} (he : 1 ≤ e) :
    a % 2 = 0 ↔ (a ^ e) % 2 = 0 := by
  constructor
  · intro ha
    have : Even (a ^ e) := by
      rw [Nat.even_pow]
      exact ⟨Nat.even_iff.2 ha, Nat.pos_iff_ne_zero.mp he⟩
    exact Nat.even_iff.1 this
  · intro h
    by_contra hne
    have ha : a % 2 = 1 := by omega
    have : (a ^ e) % 2 = 1 := pow_mod_two_of_odd ha
    omega

theorem odd_iff_pow_odd {a e : ℕ} (he : 1 ≤ e) :
    a % 2 = 1 ↔ (a ^ e) % 2 = 1 := by
  constructor
  · exact pow_mod_two_of_odd
  · exact odd_of_pow_odd he

theorem even_iff_pow_two_depth_even {a r : ℕ} :
    a % 2 = 0 ↔ (a ^ (2 ^ r)) % 2 = 0 :=
  even_iff_pow_even (Nat.one_le_pow r 2 (by decide : 0 < 2))

theorem odd_iff_pow_two_depth_odd {a r : ℕ} :
    a % 2 = 1 ↔ (a ^ (2 ^ r)) % 2 = 1 :=
  odd_iff_pow_odd (Nat.one_le_pow r 2 (by decide : 0 < 2))

/-- An exact step on a square keeps the parity of the state. -/
theorem floorPower_sq_preserves_parity {n : ℕ} (hsq : n.sqrt ^ 2 = n) :
    floorPower n % 2 = n % 2 := by
  set s := n.sqrt
  have hn : n = s ^ 2 := hsq.symm
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have himg : floorPower n = s := by
      have : floorPower (s ^ 2) = s :=
        floorPower_of_even_sq (by simpa [hn] using heven)
      simpa [hn] using this
    have hs : s % 2 = 0 :=
      (even_iff_pow_even (by decide : 1 ≤ 2)).2 (by simpa [hn] using heven)
    omega
  · have hs : s % 2 = 1 :=
      odd_of_pow_odd (by decide : 1 ≤ 2) (by simpa [hn] using hodd)
    have himg : floorPower n = s ^ 3 := by
      have : floorPower (s ^ 2) = s ^ 3 := floorPower_of_odd_sq hs
      simpa [hn] using this
    have : (s ^ 3) % 2 = 1 := pow_mod_two_of_odd hs
    omega

theorem floorPower_of_pow_two_depth_even_base {a r : ℕ} (hr : 1 ≤ r)
    (ha : a % 2 = 0) :
    floorPower (a ^ (2 ^ r)) = a ^ (2 ^ (r - 1)) ∧
      (a ^ (2 ^ (r - 1))) % 2 = 0 := by
  have hn : (a ^ (2 ^ r)) % 2 = 0 := even_iff_pow_two_depth_even.1 ha
  refine ⟨floorPower_of_pow_two_depth_even hr hn, ?_⟩
  exact even_iff_pow_two_depth_even.1 ha

theorem floorPower_of_pow_two_depth_odd_base {a r : ℕ} (hr : 1 ≤ r)
    (ha : a % 2 = 1) :
    floorPower (a ^ (2 ^ r)) = a ^ (3 * 2 ^ (r - 1)) ∧
      (a ^ (3 * 2 ^ (r - 1))) % 2 = 1 :=
  ⟨floorPower_of_pow_two_depth_odd hr ha, pow_mod_two_of_odd ha⟩

/-- Exact even or odd branch on `a^{2^r}` keeps the parity of `a`. -/
theorem floorPower_pow_two_depth_preserves_parity {a r : ℕ} (hr : 1 ≤ r) :
    floorPower (a ^ (2 ^ r)) % 2 = a % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · have h := floorPower_of_pow_two_depth_even_base hr ha
    omega
  · have h := floorPower_of_pow_two_depth_odd_base hr ha
    omega

/-- Envelope equality forces a monochrome word. -/
theorem power_bound_eq_implies_monochrome {n : ℕ} {w : List Branch}
    (hw : follows n w)
    (heq : PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) :
    w = List.replicate w.length Branch.even ∨
      w = List.replicate w.length Branch.odd := by
  induction w generalizing n with
  | nil => exact Or.inl rfl
  | cons b rest ih =>
      have hsq : n.sqrt ^ 2 = n :=
        power_bound_eq_implies_square hw heq 0 (Nat.succ_pos _)
      have hpar : floorPower n % 2 = n % 2 :=
        floorPower_sq_preserves_parity hsq
      have hfrom :=
        power_bound_eq_from (w := b :: rest) (power_bound_empty n) hw
          (by simpa [image_eq_iterate] using heq)
      have hloc : localsTight n (b :: rest) := hfrom.2
      have hrest : follows (floorPower n) rest := by
        cases b with
        | even => exact hw.2
        | odd => exact hw.2
      have htailEq :
          PowerBoundEq (floorPower^[rest.length] (floorPower n)) (floorPower n)
            rest.length (oddCount rest) :=
        localsTight_implies_power_bound_eq rest hrest hloc.2
      have hmono := ih hrest htailEq
      cases b with
      | even =>
          have heven : n % 2 = 0 := hw.1
          have himg : floorPower n % 2 = 0 := by omega
          have hrestEven : rest = List.replicate rest.length Branch.even := by
            cases hmono with
            | inl h => exact h
            | inr h =>
                cases rest with
                | nil => rfl
                | cons b' rest' =>
                    rw [List.length_cons, List.replicate_succ] at h
                    have hb' : b' = Branch.odd := (List.cons_eq_cons.mp h).1
                    have : floorPower n % 2 = 1 := by
                      rw [hb'] at hrest
                      exact hrest.1
                    omega
          refine Or.inl ?_
          rw [List.length_cons, List.replicate_succ]
          exact congrArg (List.cons Branch.even) hrestEven
      | odd =>
          have hodd : n % 2 = 1 := hw.1
          have himg : floorPower n % 2 = 1 := by omega
          have hrestOdd : rest = List.replicate rest.length Branch.odd := by
            cases hmono with
            | inr h => exact h
            | inl h =>
                cases rest with
                | nil => rfl
                | cons b' rest' =>
                    rw [List.length_cons, List.replicate_succ] at h
                    have hb' : b' = Branch.even := (List.cons_eq_cons.mp h).1
                    have : floorPower n % 2 = 0 := by
                      rw [hb'] at hrest
                      exact hrest.1
                    omega
          refine Or.inr ?_
          rw [List.length_cons, List.replicate_succ]
          exact congrArg (List.cons Branch.odd) hrestOdd

theorem floorPower_iterate_even_pow_two {a : ℕ} (ha : a % 2 = 0) :
    ∀ {k j : ℕ}, j ≤ k →
      floorPower^[j] (a ^ (2 ^ k)) = a ^ (2 ^ (k - j)) := by
  intro k j
  induction j generalizing k with
  | zero =>
      intro _
      simp
  | succ j ih =>
      intro hle
      have hk : 1 ≤ k := by omega
      rw [iterate_cons]
      have hstep : floorPower (a ^ (2 ^ k)) = a ^ (2 ^ (k - 1)) :=
        (floorPower_of_pow_two_depth_even_base hk ha).1
      rw [hstep]
      have hj : j ≤ k - 1 := by omega
      have hkj : k - 1 - j = k - (j + 1) := by
        rw [Nat.sub_right_comm, ← Nat.sub_add_eq]
      rw [ih (k := k - 1) hj, hkj]

theorem floorPower_iterate_odd_pow_two {a : ℕ} (ha : a % 2 = 1) :
    ∀ {k j : ℕ}, j ≤ k →
      floorPower^[j] (a ^ (2 ^ k)) = a ^ (3 ^ j * 2 ^ (k - j)) := by
  intro k j
  induction j generalizing a k with
  | zero =>
      intro _
      simp
  | succ j ih =>
      intro hle
      have hk : 1 ≤ k := by omega
      rw [iterate_cons]
      have hstep : floorPower (a ^ (2 ^ k)) = a ^ (3 * 2 ^ (k - 1)) :=
        (floorPower_of_pow_two_depth_odd_base hk ha).1
      rw [hstep]
      have ha3 : (a ^ 3) % 2 = 1 := pow_mod_two_of_odd ha
      have hform : a ^ (3 * 2 ^ (k - 1)) = (a ^ 3) ^ (2 ^ (k - 1)) := by
        rw [← pow_mul, mul_comm]
      rw [hform]
      have hj : j ≤ k - 1 := by omega
      have hih := ih (a := a ^ 3) (k := k - 1) ha3 hj
      have hkj : k - 1 - j = k - (j + 1) := by
        rw [Nat.sub_right_comm, ← Nat.sub_add_eq]
      rw [hih, ← pow_mul, ← mul_assoc, ← pow_succ', hkj]

theorem floorPower_iterate_even_pow_two_eq {a k : ℕ} (ha : a % 2 = 0) :
    floorPower^[k] (a ^ (2 ^ k)) = a := by
  simpa [pow_one] using floorPower_iterate_even_pow_two ha (j := k) le_rfl

theorem floorPower_iterate_odd_pow_two_eq {a k : ℕ} (ha : a % 2 = 1) :
    floorPower^[k] (a ^ (2 ^ k)) = a ^ (3 ^ k) := by
  simpa [mul_one] using floorPower_iterate_odd_pow_two ha (j := k) le_rfl

theorem follows_replicate_even_pow_two {a : ℕ} (ha : a % 2 = 0) :
    ∀ k, follows (a ^ (2 ^ k)) (List.replicate k Branch.even) := by
  intro k
  induction k with
  | zero => simp [follows]
  | succ k ih =>
      rw [List.replicate_succ]
      refine ⟨even_iff_pow_two_depth_even.1 ha, ?_⟩
      have himg : floorPower (a ^ (2 ^ (k + 1))) = a ^ (2 ^ k) := by
        simpa [Nat.add_sub_cancel] using
          (floorPower_of_pow_two_depth_even_base (Nat.succ_pos k) ha).1
      rw [himg]
      exact ih

theorem follows_replicate_odd_pow_two {a : ℕ} (ha : a % 2 = 1) :
    ∀ k, follows (a ^ (2 ^ k)) (List.replicate k Branch.odd) := by
  intro k
  induction k generalizing a ha with
  | zero => simp [follows]
  | succ k ih =>
      rw [List.replicate_succ]
      refine ⟨odd_iff_pow_two_depth_odd.1 ha, ?_⟩
      have himg : floorPower (a ^ (2 ^ (k + 1))) = (a ^ 3) ^ (2 ^ k) := by
        have h := (floorPower_of_pow_two_depth_odd_base (Nat.succ_pos k) ha).1
        rw [h, Nat.succ_sub_one, ← pow_mul, mul_comm]
      rw [himg]
      exact ih (pow_mod_two_of_odd ha)

theorem power_bound_eq_replicate_even {a k : ℕ} (ha : a % 2 = 0) :
    PowerBoundEq (floorPower^[k] (a ^ (2 ^ k))) (a ^ (2 ^ k)) k 0 := by
  unfold PowerBoundEq
  rw [floorPower_iterate_even_pow_two_eq ha, pow_zero, pow_one]

theorem power_bound_eq_replicate_odd {a k : ℕ} (ha : a % 2 = 1) :
    PowerBoundEq (floorPower^[k] (a ^ (2 ^ k))) (a ^ (2 ^ k)) k k := by
  unfold PowerBoundEq
  rw [floorPower_iterate_odd_pow_two_eq ha, ← Nat.pow_mul, ← Nat.pow_mul, mul_comm]

/-- Equality saturates iff the itinerary is an exact even or odd tower. -/
theorem power_bound_eq_iff_extremal {n : ℕ} {w : List Branch} :
    (follows n w ∧
        PowerBoundEq (floorPower^[w.length] n) n w.length (oddCount w)) ↔
      (w = List.replicate w.length Branch.even ∧
          ∃ a, a % 2 = 0 ∧ n = a ^ (2 ^ w.length)) ∨
      (w = List.replicate w.length Branch.odd ∧
          ∃ a, a % 2 = 1 ∧ n = a ^ (2 ^ w.length)) := by
  constructor
  · rintro ⟨hw, heq⟩
    have ⟨a, ha⟩ := power_bound_eq_implies_pow_two_depth hw heq
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · refine Or.inl ?_
      have hwE : w = List.replicate w.length Branch.even := by
        have hmono := power_bound_eq_implies_monochrome hw heq
        cases hmono with
        | inl h => exact h
        | inr h =>
            cases w with
            | nil => rfl
            | cons b rest =>
                rw [List.length_cons, List.replicate_succ] at h
                have hb : b = Branch.odd := (List.cons_eq_cons.mp h).1
                have : n % 2 = 1 := by
                  rw [hb] at hw
                  exact hw.1
                omega
      refine ⟨hwE, a, even_iff_pow_two_depth_even.2 (by simpa [ha] using hn), ha⟩
    · refine Or.inr ?_
      have hwO : w = List.replicate w.length Branch.odd := by
        have hmono := power_bound_eq_implies_monochrome hw heq
        cases hmono with
        | inr h => exact h
        | inl h =>
            cases w with
            | nil => rfl
            | cons b rest =>
                rw [List.length_cons, List.replicate_succ] at h
                have hb : b = Branch.even := (List.cons_eq_cons.mp h).1
                have : n % 2 = 0 := by
                  rw [hb] at hw
                  exact hw.1
                omega
      refine ⟨hwO, a, odd_iff_pow_two_depth_odd.2 (by simpa [ha] using hn), ha⟩
  · rintro (⟨hwE, a, ha, hn⟩ | ⟨hwO, a, ha, hn⟩)
    · set k := w.length
      have hwE' : w = List.replicate k Branch.even := hwE
      rw [hn, hwE']
      refine ⟨follows_replicate_even_pow_two ha k, ?_⟩
      simpa [oddCount_replicate_even] using power_bound_eq_replicate_even (k := k) ha
    · set k := w.length
      have hwO' : w = List.replicate k Branch.odd := hwO
      rw [hn, hwO']
      refine ⟨follows_replicate_odd_pow_two ha k, ?_⟩
      simpa [oddCount_replicate_odd] using power_bound_eq_replicate_odd (k := k) ha

theorem two_pow_two_pow_extremal_even (k : ℕ) :
    follows (2 ^ (2 ^ k)) (List.replicate k Branch.even) ∧
      PowerBoundEq (floorPower^[k] (2 ^ (2 ^ k))) (2 ^ (2 ^ k)) k 0 :=
  ⟨follows_replicate_even_pow_two (by decide : (2 : ℕ) % 2 = 0) k,
    power_bound_eq_replicate_even (by decide : (2 : ℕ) % 2 = 0)⟩

theorem three_pow_two_pow_extremal_odd (k : ℕ) :
    follows (3 ^ (2 ^ k)) (List.replicate k Branch.odd) ∧
      PowerBoundEq (floorPower^[k] (3 ^ (2 ^ k))) (3 ^ (2 ^ k)) k k :=
  ⟨follows_replicate_odd_pow_two (by decide : (3 : ℕ) % 2 = 1) k,
    power_bound_eq_replicate_odd (by decide : (3 : ℕ) % 2 = 1)⟩

/-- Among \(n\ge 3\), an all-odd equality of length `k` is at least `3^{2^k}`. -/
theorem odd_equality_three_pow_le {n k : ℕ} (hn : 3 ≤ n)
    (hw : follows n (List.replicate k Branch.odd))
    (heq : PowerBoundEq (floorPower^[k] n) n k k) :
    3 ^ (2 ^ k) ≤ n := by
  cases k with
  | zero =>
      exact hn
  | succ k =>
      have heq' :
          PowerBoundEq (floorPower^[(List.replicate (k + 1) Branch.odd).length] n) n
            (List.replicate (k + 1) Branch.odd).length
            (oddCount (List.replicate (k + 1) Branch.odd)) := by
        simpa [List.length_replicate, oddCount_replicate_odd] using heq
      have ⟨a, ha⟩ :=
        power_bound_eq_implies_pow_two_depth
          (w := List.replicate (k + 1) Branch.odd) hw heq'
      have hodd : n % 2 = 1 := by
        rw [List.replicate_succ] at hw
        exact hw.1
      have haodd : a % 2 = 1 :=
        odd_iff_pow_two_depth_odd.2 (by simpa [ha] using hodd)
      have ha3 : 3 ≤ a := by
        by_contra hlt
        have : a ≤ 2 := by omega
        interval_cases a
        · have : n = 0 := by simp [ha]
          omega
        · have : n = 1 := by simp [ha]
          omega
        · have : n % 2 = 0 := by
            rw [ha]
            exact even_iff_pow_two_depth_even.1 rfl
          omega
      have : 3 ^ (2 ^ (k + 1)) ≤ a ^ (2 ^ (k + 1)) :=
        Nat.pow_le_pow_left ha3 _
      simpa [ha] using this

end Problems.Juggler
