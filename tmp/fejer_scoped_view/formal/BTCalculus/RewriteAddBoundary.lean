/-
Restricted Add/carry exclusion (Claim B).

No AC-matching library. No quantification over arbitrary rewrite
engines. Coefficient-word confluence remains `Confluence.lean`.
-/

import BTCalculus.Algebra
import BTCalculus.Rewrite

namespace BTCalculus

/-! ### B1. Carry identity -/

theorem carry_of_add (x y : ℤ) :
    DZ (x + y) - DZ x - DZ y = (addDigit (lsdZ x) (lsdZ y)).2 := by
  have h := D_add x y
  linarith

theorem DZ_zero : DZ 0 = 0 := by
  simp [DZ, lsdZ]

theorem DZ_one : DZ 1 = 0 := by
  simp [DZ, lsdZ]

theorem DZ_two : DZ 2 = 1 := by
  simp [DZ, lsdZ]

/-- Carry-free D-through-Add is unsound. Witness `(1,1)`. -/
theorem D_add_unsound : DZ ((1 : ℤ) + 1) ≠ DZ 1 + DZ 1 := by
  simp [DZ_two, DZ_one]

/-! ### B2. The next state of Add is not local through D -/

/-- A binary integer output is D-local when it factors through the
`D`-images of its arguments. -/
def DLocal (H : ℤ → ℤ → ℤ) : Prop :=
  ∃ G : ℤ → ℤ → ℤ, ∀ x y, H x y = G (DZ x) (DZ y)

/-- The next state `D(x+y)` is not D-local: `D(0+0)=0` and
`D(1+1)=1` while `D(0)=D(1)=0`. -/
theorem add_not_DLocal : ¬ DLocal fun x y => DZ (x + y) := by
  rintro ⟨G, hG⟩
  have h00 := hG 0 0
  have h11 := hG 1 1
  simp [DZ_zero, DZ_one, DZ_two] at h00 h11
  exact absurd (h11.trans h00.symm) (by decide : (1 : ℤ) ≠ 0)

/-! ### B3. Constructor-sum classification -/

/-- Affine unary constructors `{S, I+, I−, N}`. `I0` is `S`. -/
inductive AffineCtor
  | S
  | Ip
  | Im
  | N
  deriving DecidableEq, Repr

namespace AffineCtor

def slope : AffineCtor → ℤ
  | S | Ip | Im => 3
  | N => -1

def const : AffineCtor → ℤ
  | S | N => 0
  | Ip => 1
  | Im => -1

def apply (U : AffineCtor) (t : ℤ) : ℤ :=
  U.slope * t + U.const

theorem apply_S (t : ℤ) : S.apply t = 3 * t := by
  simp [apply, slope, const]

theorem apply_Ip (t : ℤ) : Ip.apply t = 1 + 3 * t := by
  simp [apply, slope, const]; ring

theorem apply_Im (t : ℤ) : Im.apply t = -1 + 3 * t := by
  simp [apply, slope, const]; ring

theorem apply_N (t : ℤ) : N.apply t = -t := by
  simp [apply, slope, const]

/-- Exact constructor-sum identity, as a coefficient condition. -/
def exactTriple (U V W : AffineCtor) : Prop :=
  U.slope = W.slope ∧ V.slope = W.slope ∧ U.const + V.const = W.const

theorem apply_add_eq_iff (U V W : AffineCtor) :
    (∀ x y : ℤ, U.apply x + V.apply y = W.apply (x + y)) ↔
      exactTriple U V W := by
  constructor
  · intro h
    have h00 := h 0 0
    have h10 := h 1 0
    have h01 := h 0 1
    simp [apply] at h00 h10 h01
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · intro ⟨hsU, hsV, hc⟩ x y
    simp [apply, hsU, hsV]
    linarith

/-- The six parameterized rows, written as the eight concrete triples
(`I_a` is a parameter in the informal statement). -/
theorem exactTriple_characterization (U V W : AffineCtor) :
    exactTriple U V W ↔
      (U = S ∧ V = S ∧ W = S) ∨
      (U = N ∧ V = N ∧ W = N) ∨
      (U = Ip ∧ V = S ∧ W = Ip) ∨
      (U = S ∧ V = Ip ∧ W = Ip) ∨
      (U = Im ∧ V = S ∧ W = Im) ∨
      (U = S ∧ V = Im ∧ W = Im) ∨
      (U = Ip ∧ V = Im ∧ W = S) ∨
      (U = Im ∧ V = Ip ∧ W = S) := by
  cases U <;> cases V <;> cases W <;> simp [exactTriple, slope, const]

theorem exact_SS : ∀ x y, S.apply x + S.apply y = S.apply (x + y) :=
  (apply_add_eq_iff _ _ _).mpr (by simp [exactTriple, slope, const])

theorem exact_NN : ∀ x y, N.apply x + N.apply y = N.apply (x + y) :=
  (apply_add_eq_iff _ _ _).mpr (by simp [exactTriple, slope, const])

end AffineCtor

/-! ### B4. Same-sign residue and mixed N -/

theorem Ip_plus_Ip (x y : ℤ) :
    AffineCtor.Ip.apply x + AffineCtor.Ip.apply y =
      AffineCtor.S.apply (x + y) + 2 := by
  simp [AffineCtor.apply, AffineCtor.slope, AffineCtor.const]
  ring

theorem Im_plus_Im (x y : ℤ) :
    AffineCtor.Im.apply x + AffineCtor.Im.apply y =
      AffineCtor.S.apply (x + y) + (-2) := by
  simp [AffineCtor.apply, AffineCtor.slope, AffineCtor.const]
  ring

theorem two_not_ctor_const (W : AffineCtor) : W.const ≠ 2 := by
  cases W <;> simp [AffineCtor.const]

theorem not_exact_Ip_Ip (W : AffineCtor) :
    ¬ AffineCtor.exactTriple .Ip .Ip W := by
  cases W <;> simp [AffineCtor.exactTriple, AffineCtor.slope, AffineCtor.const]

theorem not_exact_Im_Im (W : AffineCtor) :
    ¬ AffineCtor.exactTriple .Im .Im W := by
  cases W <;> simp [AffineCtor.exactTriple, AffineCtor.slope, AffineCtor.const]

theorem not_exact_N_S (W : AffineCtor) :
    ¬ AffineCtor.exactTriple .N .S W := by
  cases W <;> simp [AffineCtor.exactTriple, AffineCtor.slope, AffineCtor.const]

/-! ### B5. Named push-in peak -/

/-- Terms of the named carry-free push-in system. -/
inductive AddTree
  | X
  | Y
  | D : AddTree → AddTree
  | S : AddTree → AddTree
  | add : AddTree → AddTree → AddTree
  deriving DecidableEq, Repr

/-- Unary `D∘S` plus push-in `S` through `Add`, with congruence.
No `D`-through-`Add` rule. -/
inductive PushInStep : AddTree → AddTree → Prop
  | d_s {t} : PushInStep (.D (.S t)) t
  | s_add {t u} : PushInStep (.S (.add t u)) (.add (.S t) (.S u))
  | cong_D {t u} : PushInStep t u → PushInStep (.D t) (.D u)
  | cong_S {t u} : PushInStep t u → PushInStep (.S t) (.S u)
  | cong_add_l {t t' u} : PushInStep t t' → PushInStep (.add t u) (.add t' u)
  | cong_add_r {t u u'} : PushInStep u u' → PushInStep (.add t u) (.add t u')

def pushInPeak : AddTree := .D (.S (.add .X .Y))

theorem pushIn_left : PushInStep pushInPeak (.add .X .Y) :=
  PushInStep.d_s

theorem pushIn_right :
    PushInStep pushInPeak (.D (.add (.S .X) (.S .Y))) :=
  PushInStep.cong_D PushInStep.s_add

theorem not_step_add_XY {u : AddTree} (h : PushInStep (.add .X .Y) u) :
    False := by
  cases h with
  | cong_add_l h => cases h
  | cong_add_r h => cases h

theorem not_step_d_add_SX_SY {u : AddTree}
    (h : PushInStep (.D (.add (.S .X) (.S .Y))) u) : False := by
  cases h with
  | cong_D h =>
    cases h with
    | cong_add_l h =>
      cases h with
      | cong_S h => cases h
    | cong_add_r h =>
      cases h with
      | cong_S h => cases h

theorem pushIn_descendants_distinct :
    AddTree.add .X .Y ≠ .D (.add (.S .X) (.S .Y)) := by
  intro h
  cases h

/-- The named carry-free push-in system is not locally confluent:
`D(S(X+Y))` has two distinct irreducibles. -/
theorem pushIn_not_locally_confluent :
    PushInStep pushInPeak (.add .X .Y) ∧
      PushInStep pushInPeak (.D (.add (.S .X) (.S .Y))) ∧
      AddTree.add .X .Y ≠ .D (.add (.S .X) (.S .Y)) ∧
      (∀ u, ¬ PushInStep (.add .X .Y) u) ∧
      (∀ u, ¬ PushInStep (.D (.add (.S .X) (.S .Y))) u) :=
  ⟨pushIn_left, pushIn_right, pushIn_descendants_distinct,
    fun _ h => not_step_add_XY h,
    fun _ h => not_step_d_add_SX_SY h⟩

/-- Both descendants evaluate to `x+y` as integers. Semantic twins. -/
theorem pushIn_peak_semantic (x y : ℤ) :
    DZ (SZ (x + y)) = x + y ∧ DZ (SZ x + SZ y) = x + y := by
  constructor
  · exact rewrite_D_S (x + y)
  · have : SZ x + SZ y = SZ (x + y) := by
      simp [SZ]; ring
    rw [this]
    exact rewrite_D_S (x + y)

/-! ### Restricted exclusion -/

/-- Packaged Add boundary: `D ∘ Add` is not D-local, same-sign `I_a`
is not a constructor identity, and the named carry-free push-in
extension fails local confluence. -/
theorem add_requires_carry_state :
    ¬ DLocal (fun x y => DZ (x + y)) ∧
      (∀ W, ¬ AffineCtor.exactTriple .Ip .Ip W) ∧
      (∀ W, ¬ AffineCtor.exactTriple .Im .Im W) ∧
      PushInStep pushInPeak (.add .X .Y) ∧
      PushInStep pushInPeak (.D (.add (.S .X) (.S .Y))) ∧
      (∀ u, ¬ PushInStep (.add .X .Y) u) ∧
      (∀ u, ¬ PushInStep (.D (.add (.S .X) (.S .Y))) u) :=
  ⟨add_not_DLocal, not_exact_Ip_Ip, not_exact_Im_Im,
    pushIn_left, pushIn_right,
    fun _ h => not_step_add_XY h,
    fun _ h => not_step_d_add_SX_SY h⟩

end BTCalculus
