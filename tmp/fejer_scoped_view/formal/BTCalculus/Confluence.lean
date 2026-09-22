import Mathlib.Logic.Relation
import BTCalculus.NormalizedDerivative

namespace BTCalculus

open Relation (ReflTransGen Join)

/-!
Confluence of the coefficient-vector rewrite, **modulo high-zero stripping**.

Python `CoeffWord` drops trailing high zeros. On raw Lean lists the
overlapping pair `[-5, 2]` forks to `[1, 0]` and `[1, 0, 0]`, both trit
words of value `1`. After `stripHigh` they are the same word `[1]`.

The engine is uniqueness of the stripped trit form: it equals
`encodeZ(value)`. Strategy A is a constructive path to that form, so
every pair of descendants joins there. Local confluence of the `i` /
`i+1` overlap is the same uniqueness, specialised to a one-step fork.
-/

instance (c : ℤ) : Decidable (isTrit c) :=
  inferInstanceAs (Decidable (c = -1 ∨ c = 0 ∨ c = 1))

/-! ### High-zero stripping (Python `CoeffWord`) -/

def stripHigh : List ℤ → List ℤ
  | [] => [0]
  | [x] => [x]
  | x :: y :: ys =>
      let t := stripHigh (y :: ys)
      if t = [0] then (if x = 0 then [0] else [x]) else x :: t

theorem stripHigh_nil : stripHigh [] = [0] := rfl

theorem stripHigh_singleton (x : ℤ) : stripHigh [x] = [x] := rfl

theorem stripHigh_ne_nil (cs : List ℤ) : stripHigh cs ≠ [] := by
  cases cs with
  | nil => simp [stripHigh]
  | cons x xs =>
    cases xs with
    | nil => simp [stripHigh]
    | cons y ys =>
      simp [stripHigh]
      split_ifs <;> simp

theorem stripHigh_cons_cons (x y : ℤ) (ys : List ℤ) :
    stripHigh (x :: y :: ys) =
      let t := stripHigh (y :: ys)
      if t = [0] then (if x = 0 then [0] else [x]) else x :: t :=
  rfl

theorem stripHigh_value : ∀ cs : List ℤ, coeffValue (stripHigh cs) = coeffValue cs
  | [] => rfl
  | [x] => rfl
  | x :: y :: ys => by
      have ih : coeffValue (stripHigh (y :: ys)) = coeffValue (y :: ys) :=
        stripHigh_value (y :: ys)
      rw [stripHigh_cons_cons]
      by_cases ht : stripHigh (y :: ys) = [0]
      · rw [if_pos ht]
        have hv : coeffValue (y :: ys) = 0 := by
          rw [← ih, ht]; rfl
        by_cases hx : x = 0
        · rw [if_pos hx]
          simpa [coeffValue, hx] using hv
        · rw [if_neg hx]
          simpa [coeffValue] using hv
      · rw [if_neg ht]
        change x + 3 * coeffValue (stripHigh (y :: ys)) = x + 3 * coeffValue (y :: ys)
        rw [ih]

theorem stripHigh_cons_ne {r : ℤ} {cs : List ℤ} (h : stripHigh cs ≠ [0]) :
    stripHigh (r :: cs) = r :: stripHigh cs := by
  cases cs with
  | nil =>
    simp [stripHigh] at h
  | cons y ys =>
    rw [stripHigh_cons_cons, if_neg h]

theorem stripHigh_idem (cs : List ℤ) : stripHigh (stripHigh cs) = stripHigh cs := by
  cases cs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      rw [stripHigh_cons_cons]
      by_cases ht : stripHigh (y :: ys) = [0]
      · rw [if_pos ht]
        by_cases hx : x = 0
        · rw [if_pos hx]; rfl
        · rw [if_neg hx]; rfl
      · rw [if_neg ht]
        have ih := stripHigh_idem (y :: ys)
        rw [stripHigh_cons_ne (by simpa [ih] using ht), ih]

theorem stripHigh_cons_stripHigh (r : ℤ) :
    ∀ cs : List ℤ, stripHigh (r :: stripHigh cs) = stripHigh (r :: cs)
  | [] => by
      change stripHigh [r, 0] = [r]
      simp [stripHigh]
      by_cases hr : r = 0
      · simp [hr]
      · simp [hr]
  | [x] => rfl
  | x :: y :: ys => by
      rw [stripHigh_cons_cons]
      by_cases ht : stripHigh (y :: ys) = [0]
      · rw [if_pos ht]
        by_cases hx : x = 0
        · rw [if_pos hx]
          subst hx
          have hinner : stripHigh (0 :: y :: ys) = [0] := by
            rw [stripHigh_cons_cons, if_pos ht]; rfl
          change stripHigh [r, 0] = stripHigh (r :: 0 :: y :: ys)
          have hR : stripHigh (r :: 0 :: y :: ys) = stripHigh [r, 0] := by
            rw [stripHigh_cons_cons, if_pos (by simpa using hinner)]
            rfl
          exact hR.symm
        · rw [if_neg hx]
          have hinner : stripHigh (x :: y :: ys) = [x] := by
            rw [stripHigh_cons_cons, if_pos ht, if_neg hx]
          have hxne : [x] ≠ [0] := by simp [hx]
          have hL : stripHigh [r, x] = r :: [x] := by
            simp [stripHigh, hxne]
          have hR : stripHigh (r :: x :: y :: ys) = r :: [x] := by
            rw [stripHigh_cons_cons, if_neg (by rw [hinner]; exact hxne), hinner]
          exact hL.trans hR.symm
      · rw [if_neg ht]
        have hinner : stripHigh (x :: y :: ys) = x :: stripHigh (y :: ys) := by
          rw [stripHigh_cons_cons, if_neg ht]
        have htail_ne : stripHigh (y :: ys) ≠ [] := stripHigh_ne_nil (y :: ys)
        have hne : x :: stripHigh (y :: ys) ≠ [0] := by
          intro h0
          exact htail_ne (List.cons.inj h0).2
        have hL : stripHigh (r :: x :: stripHigh (y :: ys)) =
            r :: x :: stripHigh (y :: ys) := by
          have ht' : stripHigh (stripHigh (y :: ys)) ≠ [0] := by
            rw [stripHigh_idem]; exact ht
          have hs : stripHigh (x :: stripHigh (y :: ys)) =
              x :: stripHigh (y :: ys) := by
            have h := stripHigh_cons_ne (r := x) ht'
            simpa [stripHigh_idem] using h
          have hne2 : stripHigh (x :: stripHigh (y :: ys)) ≠ [0] := by
            rw [hs]; exact hne
          rw [stripHigh_cons_ne (r := r) hne2, hs]
        have hR : stripHigh (r :: x :: y :: ys) = r :: x :: stripHigh (y :: ys) := by
          have hne' : stripHigh (x :: y :: ys) ≠ [0] := by
            rw [hinner]; exact hne
          rw [stripHigh_cons_cons, if_neg hne', hinner]
        exact hL.trans hR.symm

theorem stripHigh_length_le : ∀ cs : List ℤ, cs ≠ [] → (stripHigh cs).length ≤ cs.length
  | [], h => (h rfl).elim
  | [_x], _ => by simp [stripHigh]
  | x :: y :: ys, _ => by
      have ih := stripHigh_length_le (y :: ys) (List.cons_ne_nil _ _)
      rw [stripHigh_cons_cons]
      by_cases ht : stripHigh (y :: ys) = [0]
      · rw [if_pos ht]
        by_cases hx : x = 0
        · rw [if_pos hx]; simp
        · rw [if_neg hx]; simp
      · rw [if_neg ht]
        exact Nat.succ_le_succ ih

theorem encodeZ_eq_zero {n : ℤ} : encodeZ n = [0] ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg coeffValue h
    simpa [encodeZ_value, coeffValue] using this
  · intro h
    subst h
    exact encodeZ_zero

/-! ### Unique stripped trit word -/

theorem lsdZ_of_trit {c : ℤ} (h : isTrit c) : lsdZ c = c :=
  lsdZ_unique h (Int.ModEq.refl c)

theorem encodeZ_of_trit {c : ℤ} (h : isTrit c) : encodeZ c = [c] := by
  rcases h with h | h | h
  · subst h
    have hne : (-1 : ℤ) ≠ 0 := by decide
    rw [encodeZ_of_ne_zero hne, trit_DZ (Or.inl rfl), lsdZ_of_trit (Or.inl rfl)]
    simp
  · subst h
    exact encodeZ_zero
  · subst h
    have hne : (1 : ℤ) ≠ 0 := by decide
    rw [encodeZ_of_ne_zero hne, trit_DZ (Or.inr (Or.inr rfl)),
      lsdZ_of_trit (Or.inr (Or.inr rfl))]
    simp

theorem encodeZ_trit_mul3 {r m : ℤ} (hr : isTrit r) (hm : m ≠ 0) :
    encodeZ (r + 3 * m) = r :: encodeZ m := by
  have hn : r + 3 * m ≠ 0 := by
    intro h0
    have hrabs : r.natAbs ≤ 1 := by
      rcases hr with h | h | h <;> simp [h]
    have hmpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
    have hrw : r = -(3 * m) := by linarith
    have : r.natAbs = 3 * m.natAbs := by
      simp [hrw, Int.natAbs_neg, Int.natAbs_mul]
    omega
  have hlsd : lsdZ (r + 3 * m) = r := by
    rw [lsdZ_add_mul3, lsdZ_of_trit hr]
  have hdz : DZ (r + 3 * m) = m := by
    rw [DZ_add_mul3, trit_DZ hr, zero_add]
  rw [encodeZ_of_ne_zero hn, hdz, if_neg hm, hlsd]

theorem encodeZ_stripped (n : ℤ) : stripHigh (encodeZ n) = encodeZ n := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    by_cases hz : n = 0
    · subst hz
      simp [encodeZ_zero, stripHigh]
    · have hform := encodeZ_of_ne_zero hz
      by_cases hq : DZ n = 0
      · simp [hform, hq, stripHigh]
      · have hih := ih (DZ n).natAbs (by
          have := DZ_natAbs_lt hz
          omega) (DZ n) rfl
        have hne : encodeZ (DZ n) ≠ [0] := fun he => hq (encodeZ_eq_zero.mp he)
        rw [hform, if_neg hq, stripHigh_cons_ne (by simpa [hih] using hne), hih]

theorem stripHigh_trit_encodeZ {r m : ℤ} (hr : isTrit r) :
    stripHigh (r :: encodeZ m) = encodeZ (r + 3 * m) := by
  by_cases hm : m = 0
  · subst hm
    rw [encodeZ_zero]
    have hr0 : stripHigh [r, 0] = encodeZ r := by
      simp [stripHigh, encodeZ_of_trit hr]
      by_cases hz : r = 0
      · simp [hz]
      · simp [hz]
    exact hr0.trans (by simp)
  · rw [encodeZ_trit_mul3 hr hm]
    have hne : encodeZ m ≠ [0] := fun he => hm (encodeZ_eq_zero.mp he)
    rw [stripHigh_cons_ne (by simpa [encodeZ_stripped m] using hne), encodeZ_stripped]

theorem stripped_trits_eq_encodeZ :
    ∀ cs : List ℤ, allTrits cs → stripHigh cs = cs → cs = encodeZ (coeffValue cs)
  | [], _ht, hs => by
      simp [stripHigh] at hs
  | [x], ht, _hs => by
      have hx : isTrit x := by simpa [allTrits] using ht
      simp [coeffValue, encodeZ_of_trit hx]
  | x :: y :: ys, ht, hs => by
      have hx : isTrit x := ht.1
      have htl : allTrits (y :: ys) := ht.2
      have ht0 : stripHigh (y :: ys) ≠ [0] := by
        intro heq
        simp only [stripHigh_cons_cons, heq] at hs
        split_ifs at hs <;> cases hs
      have hst : stripHigh (y :: ys) = y :: ys := by
        have hcons := stripHigh_cons_ne (r := x) ht0
        simp only [hcons] at hs
        exact (List.cons_inj_right x).mp hs
      have ih := stripped_trits_eq_encodeZ (y :: ys) htl hst
      have hm : coeffValue (y :: ys) ≠ 0 := by
        intro hz
        have : y :: ys = [0] := by
          simpa [hz, encodeZ_zero] using ih
        exact ht0 (hst.trans this)
      have hv : coeffValue (x :: y :: ys) = x + 3 * coeffValue (y :: ys) := rfl
      rw [hv, encodeZ_trit_mul3 hx hm]
      exact congrArg (List.cons x) ih

/-! ### Rewrite relation on stripped words -/

def legal (cs : List ℤ) (i : ℕ) : Prop := ¬ isTrit (getCoeff cs i)

def rewriteAt (cs : List ℤ) (i : ℕ) : List ℤ := stripHigh (step cs i)

def Step (x y : List ℤ) : Prop := ∃ i, legal x i ∧ y = rewriteAt x i

theorem getCoeff_of_not_lt {cs : List ℤ} {i : ℕ} (h : ¬ i < cs.length) :
    getCoeff cs i = 0 := by
  induction cs generalizing i with
  | nil => simp [getCoeff]
  | cons _x xs ih =>
    cases i with
    | zero => simp [List.length_cons] at h
    | succ n =>
        simp [getCoeff, List.getD] at h ⊢
        exact ih (by omega)

theorem legal_lt_length {cs : List ℤ} {i : ℕ} (h : legal cs i) : i < cs.length := by
  by_contra hlen
  have : isTrit (getCoeff cs i) := by
    simp [getCoeff_of_not_lt hlen, isTrit]
  exact h this

theorem legal_zero {c : ℤ} {cs : List ℤ} (h : ¬ isTrit c) : legal (c :: cs) 0 := by
  simpa [legal, getCoeff] using h

theorem rewriteAt_stripped (cs : List ℤ) (i : ℕ) :
    stripHigh (rewriteAt cs i) = rewriteAt cs i :=
  stripHigh_idem (step cs i)

theorem rewriteAt_value (cs : List ℤ) (i : ℕ) :
    coeffValue (rewriteAt cs i) = coeffValue cs := by
  simp [rewriteAt, stripHigh_value, step_value]

theorem Step_value {x y : List ℤ} (h : Step x y) : coeffValue y = coeffValue x := by
  obtain ⟨i, _, rfl⟩ := h
  exact rewriteAt_value x i

theorem rtc_value {x y : List ℤ} (h : ReflTransGen Step x y) :
    coeffValue y = coeffValue x := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (Step_value hstep).trans ih

theorem rtc_stripped {x y : List ℤ} (hx : stripHigh x = x)
    (h : ReflTransGen Step x y) : stripHigh y = y := by
  induction h with
  | refl => exact hx
  | tail _ hstep _ih =>
      obtain ⟨i, _, rfl⟩ := hstep
      exact rewriteAt_stripped _ i

/-! ### General lex decrease; lifting a trit head -/

theorem step_lex {cs : List ℤ} {i : ℕ} (h : legal cs i) :
    List.Lex (· < ·) (absList (step cs i)) (absList cs) := by
  induction cs generalizing i with
  | nil =>
    have : isTrit (getCoeff [] i) := by simp [getCoeff, isTrit]
    exact absurd this h
  | cons c rest ih =>
    cases i with
    | zero =>
      exact step_lex_zero rest (by simpa [legal, getCoeff] using h)
    | succ n =>
      exact step_lex_succ (ih (by simpa [legal, getCoeff] using h))

theorem addHead_add (p q : ℤ) : ∀ cs, addHead p (addHead q cs) = addHead (p + q) cs
  | [] => by simp [addHead]; ring
  | _c :: _cs => by simp [addHead]; ring

theorem addHead_length (q : ℤ) : ∀ cs : List ℤ,
    (addHead q cs).length = if cs = [] then 1 else cs.length
  | [] => by simp [addHead]
  | _ :: _ => by simp [addHead]

theorem step_succ (c : ℤ) (cs : List ℤ) (n : ℕ) :
    step (c :: cs) (n + 1) = c :: step cs n :=
  rfl

theorem lift_one {r : ℤ} (_hr : isTrit r) {cs : List ℤ} {i : ℕ}
    (hs : stripHigh cs = cs) (h : legal cs i) :
    Step (stripHigh (r :: cs)) (stripHigh (r :: rewriteAt cs i)) := by
  have htail : stripHigh cs ≠ [0] := by
    intro he
    rw [hs] at he
    subst he
    have : isTrit (getCoeff [0] i) := by simp [getCoeff, isTrit]
    exact h this
  have hcons : stripHigh (r :: cs) = r :: cs := by
    rw [stripHigh_cons_ne htail, hs]
  refine ⟨i + 1, ?_, ?_⟩
  · simpa [legal, getCoeff, hcons] using h
  · rw [hcons]
    simp [rewriteAt, step_succ, stripHigh_cons_stripHigh]

theorem lift_rtc {r : ℤ} (hr : isTrit r) {cs ds : List ℤ}
    (h : ReflTransGen Step (stripHigh cs) ds) :
    ReflTransGen Step (stripHigh (r :: cs)) (stripHigh (r :: ds)) := by
  induction h with
  | refl =>
      simpa [stripHigh_cons_stripHigh] using
        (ReflTransGen.refl : ReflTransGen Step (stripHigh (r :: cs)) (stripHigh (r :: cs)))
  | @tail b c hab hstep ih =>
      obtain ⟨i, hleg, rfl⟩ := hstep
      have hb : stripHigh b = b := rtc_stripped (stripHigh_idem cs) hab
      exact ReflTransGen.tail ih (lift_one hr hb hleg)

/-! ### Strategy A reaches `encodeZ` -/

theorem reaches_singleton (n : ℤ) :
    ReflTransGen Step (stripHigh [n]) (encodeZ n) := by
  induction k : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    rw [stripHigh_singleton]
    by_cases ht : isTrit n
    · simpa [encodeZ_of_trit ht] using
        (ReflTransGen.refl : ReflTransGen Step [n] [n])
    · have hn0 : n ≠ 0 := fun hz => by
        subst hz
        exact ht (Or.inr (Or.inl rfl))
      have hleg : legal [n] 0 := legal_zero ht
      have hstep : Step [n] (rewriteAt [n] 0) := ⟨0, hleg, rfl⟩
      have hrw : rewriteAt [n] 0 = stripHigh [lsdZ n, DZ n] := by
        simp [rewriteAt, step, stepZero, addHead]
      have hr : isTrit (lsdZ n) := isTrit_lsdZ n
      by_cases hq : DZ n = 0
      · have hnf : encodeZ n = [lsdZ n] := by
          rw [encodeZ_of_ne_zero hn0, if_pos hq]
        have hdest : rewriteAt [n] 0 = [lsdZ n] := by
          rw [hrw, hq]
          simp [stripHigh]
          by_cases hr0 : lsdZ n = 0
          · simp [hr0]
          · simp [hr0]
        rw [hnf]
        exact ReflTransGen.single (hdest ▸ hstep)
      · have hpair : stripHigh [lsdZ n, DZ n] = [lsdZ n, DZ n] := by
          have hne : [DZ n] ≠ [0] := by
            intro h0
            exact hq (List.head_eq_of_cons_eq h0)
          simp [stripHigh, hne]
        have ihd := ih (DZ n).natAbs (by
          have := DZ_natAbs_lt hn0
          omega) (DZ n) rfl
        simp only [stripHigh_singleton] at ihd
        have hlift := lift_rtc (r := lsdZ n) hr (cs := [DZ n])
          (by simpa [stripHigh_singleton] using ihd)
        have hend : stripHigh (lsdZ n :: encodeZ (DZ n)) = encodeZ n := by
          rw [stripHigh_trit_encodeZ hr]
          congr 1
          exact (decomp n).symm
        have hpath : ReflTransGen Step [lsdZ n, DZ n] (encodeZ n) := by
          rw [← hpair]
          convert hlift
          exact hend.symm
        have hstep' : Step [n] [lsdZ n, DZ n] := hrw.trans hpair ▸ hstep
        exact ReflTransGen.head hstep' hpath

theorem reaches_encodeZ (cs : List ℤ) :
    ReflTransGen Step (stripHigh cs) (encodeZ (coeffValue cs)) := by
  induction n : cs.length using Nat.strong_induction_on generalizing cs with
  | h n ih =>
    match cs with
    | [] =>
        simp [stripHigh, coeffValue, encodeZ_zero]
        exact ReflTransGen.refl
    | [c] =>
        simpa [coeffValue] using reaches_singleton c
    | c :: d :: rest =>
        subst n
        by_cases ht : isTrit c
        · have hlen : (d :: rest).length < (c :: d :: rest).length := by simp
          have ihd := ih _ hlen (d :: rest) rfl
          have hlift := lift_rtc ht ihd
          have hend : stripHigh (c :: encodeZ (coeffValue (d :: rest))) =
              encodeZ (coeffValue (c :: d :: rest)) := by
            simpa [coeffValue] using
              (stripHigh_trit_encodeZ (r := c) (m := coeffValue (d :: rest)) ht)
          convert hlift
          exact hend.symm
        · have hc0 : c ≠ 0 := fun hz => by
            subst hz
            exact ht (Or.inr (Or.inl rfl))
          let tail := stripHigh (d :: rest)
          by_cases htail0 : tail = [0]
          · have hsh : stripHigh (c :: d :: rest) = [c] := by
              rw [stripHigh_cons_cons, show stripHigh (d :: rest) = [0] from htail0,
                if_pos rfl, if_neg hc0]
            have hv : coeffValue (c :: d :: rest) = c := by
              have hv0 : coeffValue (d :: rest) = 0 := by
                have hval := stripHigh_value (d :: rest)
                rw [show stripHigh (d :: rest) = [0] from htail0] at hval
                exact hval.symm
              simpa [coeffValue] using hv0
            have hsing := reaches_singleton c
            rw [hsh, hv]
            simpa [stripHigh_singleton] using hsing
          · have hsh : stripHigh (c :: d :: rest) = c :: tail :=
              stripHigh_cons_ne htail0
            have hleg : legal (c :: tail) 0 := legal_zero ht
            have hstep : Step (c :: tail) (rewriteAt (c :: tail) 0) := ⟨0, hleg, rfl⟩
            have hrw : rewriteAt (c :: tail) 0 =
                stripHigh (lsdZ c :: addHead (DZ c) tail) := by
              simp [rewriteAt, step, stepZero]
            have hlen' : (addHead (DZ c) tail).length < (c :: d :: rest).length := by
              cases ht' : tail with
              | nil => exact (stripHigh_ne_nil (d :: rest) ht').elim
              | cons _ xs =>
                  simp [addHead, List.length_cons]
                  have hle : tail.length ≤ (d :: rest).length :=
                    stripHigh_length_le (d :: rest) (List.cons_ne_nil _ _)
                  simp [ht'] at hle
                  omega
            have ihd := ih (addHead (DZ c) tail).length hlen' (addHead (DZ c) tail) rfl
            have hr : isTrit (lsdZ c) := isTrit_lsdZ c
            have hlift := lift_rtc hr ihd
            have hend : stripHigh (lsdZ c :: encodeZ (coeffValue (addHead (DZ c) tail))) =
                encodeZ (coeffValue (c :: d :: rest)) := by
              rw [stripHigh_trit_encodeZ hr]
              apply congrArg encodeZ
              have hvtail := addHead_value (DZ c) tail
              have hv0 := stripHigh_value (d :: rest)
              have hde := decomp c
              rw [hvtail, show coeffValue tail = coeffValue (d :: rest) from hv0]
              simp only [coeffValue]
              linarith
            have hpath : ReflTransGen Step (stripHigh (lsdZ c :: addHead (DZ c) tail))
                (encodeZ (coeffValue (c :: d :: rest))) := by
              convert hlift
              exact hend.symm
            have hstep' : Step (c :: tail)
                (stripHigh (lsdZ c :: addHead (DZ c) tail)) := hrw ▸ hstep
            have hstart : ReflTransGen Step (c :: tail)
                (encodeZ (coeffValue (c :: d :: rest))) :=
              ReflTransGen.head hstep' hpath
            rw [hsh]
            exact hstart

/-! ### Confluence -/

theorem confluence {a b c : List ℤ}
    (hb : ReflTransGen Step (stripHigh a) b)
    (hc : ReflTransGen Step (stripHigh a) c) :
    Join (ReflTransGen Step) b c := by
  have hb' : stripHigh b = b := rtc_stripped (stripHigh_idem a) hb
  have hc' : stripHigh c = c := rtc_stripped (stripHigh_idem a) hc
  have vb : coeffValue b = coeffValue a := (rtc_value hb).trans (stripHigh_value a)
  have vc : coeffValue c = coeffValue a := (rtc_value hc).trans (stripHigh_value a)
  refine ⟨encodeZ (coeffValue a), ?_, ?_⟩
  · have := reaches_encodeZ b
    rw [hb', vb] at this
    exact this
  · have := reaches_encodeZ c
    rw [hc', vc] at this
    exact this

theorem locally_confluent {a b c : List ℤ} (ha : stripHigh a = a)
    (hb : Step a b) (hc : Step a c) :
    Join (ReflTransGen Step) b c := by
  rw [← ha] at hb hc
  exact confluence (ReflTransGen.single hb) (ReflTransGen.single hc)

/-- Overlapping critical pair at sites `0` and `1` joins after stripping. -/
theorem overlap_join (c d : ℤ) (rest : List ℤ)
    (_hc : ¬ isTrit c) (_hd : ¬ isTrit d) :
    Join (ReflTransGen Step) (rewriteAt (c :: d :: rest) 0)
      (rewriteAt (c :: d :: rest) 1) := by
  refine ⟨encodeZ (coeffValue (c :: d :: rest)), ?_, ?_⟩
  · have := reaches_encodeZ (rewriteAt (c :: d :: rest) 0)
    rw [rewriteAt_stripped, rewriteAt_value] at this
    exact this
  · have := reaches_encodeZ (rewriteAt (c :: d :: rest) 1)
    rw [rewriteAt_stripped, rewriteAt_value] at this
    exact this

/-- Raw Lean lists of the overlapping pair are not equal; stripping joins them. -/
theorem overlap_minus5_two_raw :
    step [-5, 2] 0 = [1, 0] ∧
      step (step (step [-5, 2] 1) 0) 1 = [1, 0, 0] := by
  native_decide

theorem overlap_minus5_two_stripped :
    rewriteAt [-5, 2] 0 = [1] ∧
      rewriteAt (rewriteAt (rewriteAt [-5, 2] 1) 0) 1 = [1] := by
  native_decide

end BTCalculus
