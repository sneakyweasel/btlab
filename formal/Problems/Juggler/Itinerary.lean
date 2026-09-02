import Problems.Juggler.Termination

namespace Problems.Juggler

/-!
# Trajectory itinerary

`bit` is the parity observation. `word n k` is the actual length-`k`
itinerary of `n`. `follows` is the same fact as a predicate on a
combinatorial word. The bridge is

```
follows n w  ↔  word n w.length = w
```
-/

inductive Branch where
  | even
  | odd
  deriving DecidableEq, Repr

def bit (n : ℕ) : Branch :=
  if n % 2 = 0 then .even else .odd

def word : ℕ → ℕ → List Branch
  | _, 0 => []
  | n, k + 1 => bit n :: word (floorPower n) k

/-- The trajectory of `n` realizes the finite parity word `w`. -/
def follows : ℕ → List Branch → Prop
  | _, [] => True
  | n, .even :: w => n % 2 = 0 ∧ follows (floorPower n) w
  | n, .odd :: w => n % 2 = 1 ∧ follows (floorPower n) w

/-- Image of `n` after the realized word `w`. Definitional on `cons`. -/
def image : ℕ → List Branch → ℕ
  | n, [] => n
  | n, _ :: w => image (floorPower n) w

@[simp] theorem image_nil (n : ℕ) : image n [] = n := rfl

@[simp] theorem image_cons (n : ℕ) (b : Branch) (w : List Branch) :
    image n (b :: w) = image (floorPower n) w := rfl

theorem bit_even {n : ℕ} (heven : n % 2 = 0) : bit n = .even :=
  if_pos heven

theorem bit_odd {n : ℕ} (hodd : n % 2 = 1) : bit n = .odd := by
  have : n % 2 ≠ 0 := by omega
  simp [bit, this]

theorem word_zero (n : ℕ) : word n 0 = [] := rfl

theorem word_succ (n k : ℕ) :
    word n (k + 1) = bit n :: word (floorPower n) k := rfl

theorem word_length (n : ℕ) : ∀ k, (word n k).length = k
  | 0 => rfl
  | k + 1 => by simp [word_succ, word_length (floorPower n) k]

theorem follows_nil (n : ℕ) : follows n [] := trivial

theorem follows_iff_word (n : ℕ) : ∀ w : List Branch,
    follows n w ↔ word n w.length = w
  | [] => by simp [follows, word]
  | .even :: w => by
      have ih := follows_iff_word (floorPower n) w
      constructor
      · intro hw
        simp [word_succ, bit_even hw.1, ih.mp hw.2, List.length_cons]
      · intro hw
        have hbit : bit n = .even := by
          have := congrArg List.head? hw
          simp [word_succ] at this
          exact this
        have heven : n % 2 = 0 := by
          by_cases h : n % 2 = 0
          · exact h
          · have : bit n = .odd := by
              have h1 : n % 2 = 1 := by omega
              exact bit_odd h1
            exact (Branch.noConfusion (hbit.symm.trans this))
        have htail : word (floorPower n) w.length = w := by
          simpa [word_succ, bit_even heven, List.length_cons] using hw
        exact ⟨heven, ih.mpr htail⟩
  | .odd :: w => by
      have ih := follows_iff_word (floorPower n) w
      constructor
      · intro hw
        simp [word_succ, bit_odd hw.1, ih.mp hw.2, List.length_cons]
      · intro hw
        have hbit : bit n = .odd := by
          have := congrArg List.head? hw
          simp [word_succ] at this
          exact this
        have hodd : n % 2 = 1 := by
          by_cases h : n % 2 = 0
          · have : bit n = .even := bit_even h
            exact (Branch.noConfusion (hbit.symm.trans this))
          · omega
        have htail : word (floorPower n) w.length = w := by
          simpa [word_succ, bit_odd hodd, List.length_cons] using hw
        exact ⟨hodd, ih.mpr htail⟩

theorem image_eq_iterate (n : ℕ) : ∀ w, image n w = floorPower^[w.length] n := by
  intro w
  induction w generalizing n with
  | nil => simp
  | cons _b w ih =>
      simp [List.length_cons, ih, iterate_cons]

theorem image_word (n k : ℕ) : image n (word n k) = floorPower^[k] n := by
  rw [image_eq_iterate, word_length]

theorem image_append (n : ℕ) : ∀ u v, image n (u ++ v) = image (image n u) v
  | [], _ => rfl
  | _ :: u, v => by simp [image_append (floorPower n) u v]

theorem follows_append {n : ℕ} : ∀ {u v : List Branch},
    follows n u → follows (image n u) v → follows n (u ++ v)
  | [], _, _, hv => hv
  | .even :: u, v, hu, hv =>
      ⟨hu.1, follows_append (u := u) hu.2 (by simpa [image] using hv)⟩
  | .odd :: u, v, hu, hv =>
      ⟨hu.1, follows_append (u := u) hu.2 (by simpa [image] using hv)⟩

theorem follows_even_letter {m : ℕ} (he : m % 2 = 0) :
    follows m [Branch.even] :=
  ⟨he, trivial⟩

theorem follows_of_append_left {n : ℕ} :
    ∀ {u v : List Branch}, follows n (u ++ v) → follows n u
  | [], _, _ => trivial
  | .even :: u, _v, h => ⟨h.1, follows_of_append_left (u := u) h.2⟩
  | .odd :: u, _v, h => ⟨h.1, follows_of_append_left (u := u) h.2⟩

theorem follows_of_append_right {n : ℕ} :
    ∀ {u v : List Branch}, follows n (u ++ v) → follows (image n u) v
  | [], _, h => by simpa [image] using h
  | .even :: u, v, h => by
      simpa [image] using follows_of_append_right (n := floorPower n) (u := u) h.2
  | .odd :: u, v, h => by
      simpa [image] using follows_of_append_right (n := floorPower n) (u := u) h.2

theorem image_pos {n : ℕ} (hn : 1 ≤ n) : ∀ w, 1 ≤ image n w
  | [] => hn
  | _ :: w => image_pos (floorPower_pos hn) w

theorem follows_get_even {n : ℕ} :
    ∀ w, follows n w →
      ∀ i, (hi : i < w.length) → w[i] = .even → (floorPower^[i] n) % 2 = 0 := by
  intro w
  induction w generalizing n with
  | nil =>
      intro _ i hi
      cases hi
  | cons b rest ih =>
      intro hw i hi he
      cases b with
      | even =>
          cases i with
          | zero => exact hw.1
          | succ j =>
              have hj : j < rest.length := by
                simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
              have hget : (Branch.even :: rest)[j + 1] = rest[j] := rfl
              have hiter : floorPower^[j + 1] n = floorPower^[j] (floorPower n) :=
                iterate_cons n j
              have hrest : follows (floorPower n) rest := hw.2
              simpa [hget, hiter] using ih hrest j hj (hget ▸ he)
      | odd =>
          cases i with
          | zero => cases he
          | succ j =>
              have hj : j < rest.length := by
                simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
              have hget : (Branch.odd :: rest)[j + 1] = rest[j] := rfl
              have hiter : floorPower^[j + 1] n = floorPower^[j] (floorPower n) :=
                iterate_cons n j
              have hrest : follows (floorPower n) rest := hw.2
              simpa [hget, hiter] using ih hrest j hj (hget ▸ he)

theorem follows_get_odd {n : ℕ} :
    ∀ w, follows n w →
      ∀ i, (hi : i < w.length) → w[i] = .odd → (floorPower^[i] n) % 2 = 1 := by
  intro w
  induction w generalizing n with
  | nil =>
      intro _ i hi
      cases hi
  | cons b rest ih =>
      intro hw i hi ho
      cases b with
      | even =>
          cases i with
          | zero => cases ho
          | succ j =>
              have hj : j < rest.length := by
                simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
              have hget : (Branch.even :: rest)[j + 1] = rest[j] := rfl
              have hiter : floorPower^[j + 1] n = floorPower^[j] (floorPower n) :=
                iterate_cons n j
              have hrest : follows (floorPower n) rest := hw.2
              simpa [hget, hiter] using ih hrest j hj (hget ▸ ho)
      | odd =>
          cases i with
          | zero => exact hw.1
          | succ j =>
              have hj : j < rest.length := by
                simpa [List.length_cons] using Nat.succ_lt_succ_iff.mp hi
              have hget : (Branch.odd :: rest)[j + 1] = rest[j] := rfl
              have hiter : floorPower^[j + 1] n = floorPower^[j] (floorPower n) :=
                iterate_cons n j
              have hrest : follows (floorPower n) rest := hw.2
              simpa [hget, hiter] using ih hrest j hj (hget ▸ ho)

theorem follows_get {n : ℕ} {w : List Branch} (hw : follows n w)
    (i : ℕ) (hi : i < w.length) :
    (w[i] = .even → (floorPower^[i] n) % 2 = 0) ∧
    (w[i] = .odd → (floorPower^[i] n) % 2 = 1) :=
  ⟨follows_get_even w hw i hi, follows_get_odd w hw i hi⟩

theorem follows_take {n : ℕ} :
    ∀ (w : List Branch) (i : ℕ), follows n w → follows n (w.take i)
  | _, 0, _ => trivial
  | [], _i + 1, _ => trivial
  | .even :: rest, i + 1, h =>
      ⟨h.1, follows_take rest i h.2⟩
  | .odd :: rest, i + 1, h =>
      ⟨h.1, follows_take rest i h.2⟩

theorem image_take_of_le {n : ℕ} {w : List Branch} {i : ℕ}
    (hi : i ≤ w.length) :
    image n (w.take i) = floorPower^[i] n := by
  have hlen : (w.take i).length = i := List.length_take_of_le hi
  rw [image_eq_iterate, hlen]

/-- Landing in `{1,…,11}` is already fatal. -/
theorem image_lt_twelve_reachesOne {n : ℕ} {w : List Branch}
    (hn : 1 ≤ n) (h : image n w < 12) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm
    (reachesOne_of_lt_twelve (image_pos hn w) h)

theorem image_two_reachesOne {n : ℕ} {w : List Branch}
    (h : image n w = 2) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm (by rw [h]; exact two_reachesOne)

theorem image_four_reachesOne {n : ℕ} {w : List Branch}
    (h : image n w = 4) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm (by rw [h]; exact four_reachesOne)

theorem image_six_reachesOne {n : ℕ} {w : List Branch}
    (h : image n w = 6) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm (by rw [h]; exact six_reachesOne)

theorem image_eight_reachesOne {n : ℕ} {w : List Branch}
    (h : image n w = 8) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm (by rw [h]; exact eight_reachesOne)

theorem reachesOne_of_image {n : ℕ} {w : List Branch}
    (hm : ReachesOne (image n w)) : ReachesOne n :=
  reachesOne_of_iterate (image_eq_iterate n w).symm hm

/-- Boolean realization check. Definitionally recursive on the word. -/
def followsB : ℕ → List Branch → Bool
  | _, [] => true
  | n, .even :: w => (n % 2 == 0) && followsB (floorPower n) w
  | n, .odd :: w => (n % 2 == 1) && followsB (floorPower n) w

theorem followsB_iff (n : ℕ) : ∀ w, followsB n w = true ↔ follows n w
  | [] => by simp [followsB, follows]
  | .even :: w => by
      have ih := followsB_iff (floorPower n) w
      simp [followsB, follows, Bool.and_eq_true, beq_iff_eq, ih]
  | .odd :: w => by
      have ih := followsB_iff (floorPower n) w
      simp [followsB, follows, Bool.and_eq_true, beq_iff_eq, ih]

/-- `T_w` is monotone on the realizing set of `w`. -/
theorem image_monotone_of_follows :
    ∀ {w : List Branch} {n m : ℕ},
      follows n w → follows m w → n ≤ m → image n w ≤ image m w
  | [], _, _, _, _, hle => hle
  | .even :: w, _, _, hn, hm, hle =>
      image_monotone_of_follows (w := w) hn.2 hm.2
        (floorPower_even_mono hn.1 hm.1 hle)
  | .odd :: w, _, _, hn, hm, hle =>
      image_monotone_of_follows (w := w) hn.2 hm.2
        (floorPower_odd_mono hn.1 hm.1 hle)

end Problems.Juggler
