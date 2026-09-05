import Mathlib.Data.Int.Basic
import Mathlib.Tactic

set_option exponentiation.threshold 400000
set_option maxRecDepth 100000

namespace Problems.Juggler

/-!
# Run-type survivor lattice

The \(99\) lengths that survive run-type finance at the verified
descent floor \(10^6\) (Paper A Theorem 4.8) are three affine
families on the unimodular basis
\((25781,16266)\), \((1054,665)\) (Paper A Proposition 4.9).

This file certifies the integer arithmetic of that lattice: the
unimodular identity, the two Farey seeds, the generator comparison
\(3^{665}>2^{1054}\), and the three family lists. It does not prove
the finance packing, does not identify the lists with a descent
computation, and is not a halt theorem.

Dossier extract: `docs/theory/juggler_run_survivor_lattice_note.md`.
-/

/-- First surplus intermediate of \(\log 2/\log 3\). -/
def Lstar : ℤ := 25781

/-- Odd count of `Lstar`. -/
def Ostar : ℤ := 16266

/-- Continued-fraction step of \(\log 2/\log 3\). -/
def Lstep : ℤ := 1054

/-- Odd count of `Lstep`. -/
def Ostep : ℤ := 665

/-- Lattice point \(a(L_*,o_*)+b(L_{\mathrm{step}},o_{\mathrm{step}})\). -/
def latticePoint (a b : ℤ) : ℤ × ℤ :=
  (a * Lstar + b * Lstep, a * Ostar + b * Ostep)

/-- The two generators are a unimodular basis of \(\mathbb Z^2\). -/
theorem run_survivor_unimodular :
    Lstar * Ostep - Lstep * Ostar = 1 := by
  decide +kernel

/-- The generator itself is formally expanding, at the least odd count. -/
theorem three_pow_step_gt_two_pow_step :
    (3 : ℕ) ^ 665 > (2 : ℕ) ^ 1054 := by
  norm_num

theorem three_pow_pred_step_le_two_pow_step :
    (3 : ℕ) ^ 664 ≤ (2 : ℕ) ^ 1054 := by
  norm_num

/-- Next principal convergent: \(50508=2\cdot 25781-1054\). -/
theorem run_survivor_seed_F2 :
    latticePoint 2 (-1) = (50508, 31867) := by
  decide +kernel

/-- Farey sum of the two previous seeds: \(76289=3\cdot 25781-1054\). -/
theorem run_survivor_seed_F3 :
    latticePoint 3 (-1) = (76289, 48133) := by
  decide +kernel

/-- Family \(F_1\): \(a=1\), \(b=0,\ldots,28\). -/
def family1 : List (ℤ × ℤ) :=
  (List.range 29).map fun k => latticePoint 1 (k : ℤ)

/-- Family \(F_2\): \(a=2\), \(b=-1,\ldots,45\). -/
def family2 : List (ℤ × ℤ) :=
  (List.range 47).map fun k => latticePoint 2 ((k : ℤ) - 1)

/-- Family \(F_3\): \(a=3\), \(b=-1,\ldots,21\). -/
def family3 : List (ℤ × ℤ) :=
  (List.range 23).map fun k => latticePoint 3 ((k : ℤ) - 1)

/-- Packing deaths: the \(F_1\) continuation \(b=29,\ldots,70\). -/
def packingDeaths : List (ℤ × ℤ) :=
  (List.range 42).map fun k => latticePoint 1 ((k : ℤ) + 29)

/-- The \(99\) lattice points of Paper A Proposition 4.9. -/
def runSurvivors : List (ℤ × ℤ) :=
  family1 ++ family2 ++ family3

theorem family1_length : family1.length = 29 := rfl

theorem family2_length : family2.length = 47 := rfl

theorem family3_length : family3.length = 23 := rfl

theorem packingDeaths_length : packingDeaths.length = 42 := rfl

theorem runSurvivors_length : runSurvivors.length = 99 := rfl

theorem family1_first : family1.head? = some (25781, 16266) := by
  decide +kernel

theorem family1_last : family1.getLast? = some (55293, 34886) := by
  decide +kernel

theorem family2_first : family2.head? = some (50508, 31867) := by
  decide +kernel

theorem family2_last : family2.getLast? = some (98992, 62457) := by
  decide +kernel

theorem family3_first : family3.head? = some (76289, 48133) := by
  decide +kernel

theorem family3_last : family3.getLast? = some (99477, 62763) := by
  decide +kernel

theorem packingDeaths_first : packingDeaths.head? = some (56347, 35551) := by
  decide +kernel

theorem packingDeaths_last : packingDeaths.getLast? = some (99561, 62816) := by
  decide +kernel

/-- The \(99\) family lengths are pairwise distinct. -/
theorem runSurvivorLengths_nodup :
    (runSurvivors.map fun p => p.1).Nodup := by
  decide +kernel

end Problems.Juggler
