import Problems.Juggler.Iteration

namespace Problems.Juggler

/-!
# Functional-graph primitives for the Juggler map

Thin names for `floorPower` as a deterministic functional graph.
This is not a generic graph library, not a bead schema, and not a
halt theorem.
-/

/-- One directed edge of the Juggler map. -/
def JEdge (x y : ℕ) : Prop :=
  floorPower x = y

/-- The unique outgoing edge from `x`. -/
def ParentOf (x y : ℕ) : Prop :=
  JEdge x y

/-- A length-`k` forward path. -/
def JPath (x y k : ℕ) : Prop :=
  floorPower^[k] x = y

/-- Forward ancestry, including the zero-step path. -/
def Ancestor (x y : ℕ) : Prop :=
  ∃ k, JPath x y k

theorem jEdge_iff {x y : ℕ} : JEdge x y ↔ floorPower x = y :=
  Iff.rfl

theorem jEdge_of_floorPower {x y : ℕ} (h : floorPower x = y) : JEdge x y :=
  h

theorem floorPower_of_jEdge {x y : ℕ} (h : JEdge x y) : floorPower x = y :=
  h

theorem jEdge_deterministic {x y z : ℕ} (hy : JEdge x y) (hz : JEdge x z) :
    y = z :=
  hy.symm.trans hz

theorem parentOf_iff {x y : ℕ} : ParentOf x y ↔ floorPower x = y :=
  Iff.rfl

theorem jPath_zero (x : ℕ) : JPath x x 0 :=
  rfl

theorem jPath_one {x y : ℕ} (h : JEdge x y) : JPath x y 1 :=
  h

theorem jPath_succ {x y z k : ℕ} (hxy : JPath x y k) (hyz : JEdge y z) :
    JPath x z (k + 1) := by
  change floorPower^[k + 1] x = z
  rw [Function.iterate_succ_apply', hxy]
  exact hyz

theorem jPath_add {x y z k r : ℕ} (hxy : JPath x y k) (hyz : JPath y z r) :
    JPath x z (k + r) := by
  unfold JPath at *
  have hstep : floorPower^[k + r] x = floorPower^[r] (floorPower^[k] x) := by
    rw [Nat.add_comm]
    exact Function.iterate_add_apply floorPower r k x
  rw [hstep, hxy]
  exact hyz

theorem ancestor_refl (x : ℕ) : Ancestor x x :=
  ⟨0, jPath_zero x⟩

theorem ancestor_of_parent {x y : ℕ} (h : ParentOf x y) : Ancestor x y :=
  ⟨1, jPath_one h⟩

theorem ancestor_trans {x y z : ℕ} (hxy : Ancestor x y) (hyz : Ancestor y z) :
    Ancestor x z := by
  obtain ⟨k, hk⟩ := hxy
  obtain ⟨r, hr⟩ := hyz
  exact ⟨k + r, jPath_add hk hr⟩

end Problems.Juggler
