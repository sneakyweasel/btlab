import Representation.Words

namespace BTCalculus

open Representation.Words

namespace TritAlgebra

/-- Lattice order on the 3-element chain. -/
def leT (a b : Trit) : Prop := a.toInt ≤ b.toInt

def minT (a b : Trit) : Trit :=
  if a.toInt ≤ b.toInt then a else b

def maxT (a b : Trit) : Trit :=
  if a.toInt ≤ b.toInt then b else a

theorem minT_comm (a b : Trit) : minT a b = minT b a := by
  cases a <;> cases b <;> rfl

theorem maxT_comm (a b : Trit) : maxT a b = maxT b a := by
  cases a <;> cases b <;> rfl

theorem minT_assoc (a b c : Trit) : minT a (minT b c) = minT (minT a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem maxT_assoc (a b c : Trit) : maxT a (maxT b c) = maxT (maxT a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem minT_idem (a : Trit) : minT a a = a := by
  cases a <;> rfl

theorem maxT_idem (a : Trit) : maxT a a = a := by
  cases a <;> rfl

theorem absorb_min_max (a b : Trit) : minT a (maxT a b) = a := by
  cases a <;> cases b <;> rfl

theorem absorb_max_min (a b : Trit) : maxT a (minT a b) = a := by
  cases a <;> cases b <;> rfl

theorem minT_bot (a : Trit) : minT Trit.minus a = Trit.minus := by
  cases a <;> rfl

theorem maxT_top (a : Trit) : maxT Trit.plus a = Trit.plus := by
  cases a <;> rfl

theorem min_distrib_max (a b c : Trit) :
    minT a (maxT b c) = maxT (minT a b) (minT a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem max_distrib_min (a b c : Trit) :
    maxT a (minT b c) = minT (maxT a b) (maxT a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem de_morgan_min (a b : Trit) :
    (minT a b).negate = maxT a.negate b.negate := by
  cases a <;> cases b <;> rfl

theorem de_morgan_max (a b : Trit) :
    (maxT a b).negate = minT a.negate b.negate := by
  cases a <;> cases b <;> rfl

theorem negate_antitone {a b : Trit} (h : leT a b) : leT b.negate a.negate := by
  cases a <;> cases b <;> simp [leT, Trit.toInt, Trit.negate] at h ⊢

/-- Kleene inequality on the 3-element chain. -/
theorem kleene (a b : Trit) :
    leT (minT a a.negate) (maxT b b.negate) := by
  cases a <;> cases b <;> simp [leT, minT, maxT, Trit.toInt, Trit.negate]

/-- Complement laws fail: this is not a Boolean algebra. -/
theorem not_boolean_zero :
    maxT Trit.zero Trit.zero.negate ≠ Trit.plus := by
  simp [maxT, Trit.toInt, Trit.negate]

end TritAlgebra

end BTCalculus
