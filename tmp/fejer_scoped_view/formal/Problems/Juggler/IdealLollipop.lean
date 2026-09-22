import Problems.Juggler.IdealCycleMin
import Problems.Juggler.CyclePosition
import Problems.Juggler.Seam
import Problems.Juggler.Progress

namespace Problems.Juggler

/-!
# Honest cycle figure (hybrid schematic + witness)

Display source of truth for the companion lollipop. It wraps existing
CycleMin / arrival / certificate facts. It does not reprove Paper A
and is not a halt theorem.

The default figure is schematic CycleMin geometry plus an optional
stem *kind*. A `RealizedWitness` is optional: integers exist for the
sink `{1}`, captures onto `{1}`, and leftover words. There is no
compiled nontrivial `CycleItinerary`.

Collision Factorization at an arbitrary vertex is
`CyclePosition.CollisionFactorization`. The valley fork is
`Seam.SeamData`. Beads stay a projection of the cycle run list, not
a stem law.
-/

/-! ## Painted marks -/

/-- Every painted thing carries exactly one of these. -/
inductive FigureMark
  | forced
  | optional
  | unknown
  | leftover
  | offFigure
  deriving DecidableEq, Repr

/-! ## Schematic cycle -/

/-- Forced CycleMin geometry the balloon may paint. Interval *counts*
    stay unknown; leftover chips are not this circle. -/
structure CycleFigure where
  launchOO : FigureMark := .forced
  fourSureE : FigureMark := .forced
  expanding : FigureMark := .forced
  evenCountGe4 : FigureMark := .forced
  oddCountGe7 : FigureMark := .forced
  lengthGe11 : FigureMark := .forced
  a1Ge2 : FigureMark := .forced
  lastOddLe1 : FigureMark := .forced
  twoSeams : FigureMark := .forced
  firstEvenOvershoot : FigureMark := .forced
  lastEvenCell : FigureMark := .forced
  lastEvenNeOddSq : FigureMark := .forced
  valleyOdd : FigureMark := .forced
  twoSureLinks : FigureMark := .forced
  hugPrefix : FigureMark := .forced
  shapeNotCycle : FigureMark := .leftover
  deriving Repr

def schematicCycleFigure : CycleFigure := {}

theorem balloonSchema_no_unknown :
    ∀ s ∈ balloonSchema, BalloonStation.parity s ≠ .unknown := by
  decide

theorem schematicCycleFigure_forced_launch :
    schematicCycleFigure.launchOO = .forced :=
  rfl

theorem schematicCycleFigure_shape_leftover :
    schematicCycleFigure.shapeNotCycle = .leftover :=
  rfl

theorem cycleFigure_of_cycleMin {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    CycleMinShape w ∧
      (∃ rest, w = Branch.odd :: Branch.odd :: rest) ∧
        w.getLast? = some Branch.even ∧
          4 ≤ evenCount w ∧ 7 ≤ oddCount w ∧ 11 ≤ w.length :=
  ⟨cycleMin_inhabits_shape hn h,
    cycleMin_starts_two_odds hn h,
    cycleMin_getLast_even hn h,
    cycle_itinerary_even_count_ge_four hn h.1,
    cycleMin_oddCount_ge_seven hn h,
    cycle_itinerary_length_ge_eleven hn h.1⟩

/-! ## Join sites on the six sure letters -/

inductive ArrivalRigidity
  | rigid (arr : CycleArrival)
  | dependsOnFill
  deriving DecidableEq, Repr

inductive StemTerminal
  | even
  | unknown
  deriving DecidableEq, Repr

def stemTerminalOf : CycleArrival → StemTerminal
  | .oArrival => .even
  | .eArrival => .unknown

theorem oArrival_stem_terminal_even :
    stemTerminalOf .oArrival = .even :=
  rfl

theorem eArrival_stem_terminal_unknown :
    stemTerminalOf .eArrival = .unknown :=
  rfl

/-- Six sure letters plus a realized extra-letter fallback.
    Interval slots are not constructors. -/
inductive SureLetterSite
  | valley
  | launchO
  | firstE
  | middleE
  | thirdE
  | lastE
  | extraLetter
  deriving DecidableEq, Repr

def SureLetterSite.vertexParity : SureLetterSite → BeadParity
  | .valley | .launchO => .odd
  | .firstE | .middleE | .thirdE | .lastE => .even
  | .extraLetter => .unknown

/-- Schematic rigidity. Valley / launch O / first E are CycleMin
    theorems. Third E is the balloon / `assembleFill` convention
    (previous station is even). Middle / last E and a realized extra
    letter depend on the fill. -/
def SureLetterSite.rigidity : SureLetterSite → ArrivalRigidity
  | .valley => .rigid .eArrival
  | .launchO | .firstE => .rigid .oArrival
  | .thirdE => .rigid .eArrival
  | .middleE | .lastE | .extraLetter => .dependsOnFill

def SureLetterSite.isValley : SureLetterSite → Bool
  | .valley => true
  | _ => false

inductive CutForbidden
  | rotateEven
  | rotateOE
  deriving DecidableEq, Repr

/-- CycleMin *cuts* that start `E` or `OE` are forbidden. That is not
    a join-site ban. The valley *is* the CycleMin cut. -/
def SureLetterSite.cutForbiddens : SureLetterSite → List CutForbidden
  | .valley => []
  | .launchO => [.rotateOE]
  | .firstE | .middleE | .thirdE | .lastE => [.rotateEven]
  | .extraLetter => []

structure JoinFigure where
  site : SureLetterSite
  deriving DecidableEq, Repr

def JoinFigure.rigidity (J : JoinFigure) : ArrivalRigidity :=
  J.site.rigidity

def JoinFigure.terminal (J : JoinFigure) : StemTerminal :=
  match J.rigidity with
  | .rigid arr => stemTerminalOf arr
  | .dependsOnFill => .unknown

def JoinFigure.vertexParity (J : JoinFigure) : BeadParity :=
  J.site.vertexParity

def JoinFigure.isValley (J : JoinFigure) : Bool :=
  J.site.isValley

def JoinFigure.cutForbiddens (J : JoinFigure) : List CutForbidden :=
  J.site.cutForbiddens

def joinFigure (s : SureLetterSite) : JoinFigure :=
  ⟨s⟩

def sureLetterJoinTable : List JoinFigure :=
  [joinFigure .valley, joinFigure .launchO, joinFigure .firstE,
    joinFigure .middleE, joinFigure .thirdE, joinFigure .lastE]

theorem sureLetterJoinTable_length : sureLetterJoinTable.length = 6 :=
  rfl

theorem join_valley_rigid_e :
    (joinFigure .valley).rigidity = .rigid .eArrival :=
  rfl

theorem join_launchO_rigid_o :
    (joinFigure .launchO).rigidity = .rigid .oArrival :=
  rfl

theorem join_firstE_rigid_o :
    (joinFigure .firstE).rigidity = .rigid .oArrival :=
  rfl

theorem join_middleE_depends :
    (joinFigure .middleE).rigidity = .dependsOnFill :=
  rfl

theorem join_thirdE_rigid_e :
    (joinFigure .thirdE).rigidity = .rigid .eArrival :=
  rfl

theorem join_lastE_depends :
    (joinFigure .lastE).rigidity = .dependsOnFill :=
  rfl

theorem join_extraLetter_depends :
    (joinFigure .extraLetter).rigidity = .dependsOnFill :=
  rfl

theorem join_oArrival_terminal_even :
    (joinFigure .launchO).terminal = .even ∧
      (joinFigure .firstE).terminal = .even :=
  ⟨rfl, rfl⟩

theorem join_eArrival_terminal_unknown :
    (joinFigure .valley).terminal = .unknown ∧
      (joinFigure .thirdE).terminal = .unknown :=
  ⟨rfl, rfl⟩

theorem join_fill_terminal_unknown :
    (joinFigure .middleE).terminal = .unknown ∧
      (joinFigure .lastE).terminal = .unknown :=
  ⟨rfl, rfl⟩

theorem join_valley_isValley : (joinFigure .valley).isValley = true :=
  rfl

theorem join_launchO_not_valley : (joinFigure .launchO).isValley = false :=
  rfl

theorem join_launchO_cut_OE :
    (joinFigure .launchO).cutForbiddens = [.rotateOE] :=
  rfl

theorem join_firstE_cut_even :
    (joinFigure .firstE).cutForbiddens = [.rotateEven] :=
  rfl

theorem empty_interval_not_join_stop :
    ∀ s ∈ balloonSchema, s.isForced = false →
      BalloonStation.sureLetterCount s = 0 := by
  intro s _ h
  cases s with
  | sureLaunchO => simp [BalloonStation.isForced] at h
  | sureEven r =>
      cases r <;> simp [BalloonStation.isForced] at h
  | intervalOdd k =>
      cases k <;> rfl
  | intervalExtraEven => rfl

/-! ## CycleMin rigidity of valley, launch O, first E -/

theorem cycleMin_has_index_one {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) : 1 < w.length := by
  have := cycle_itinerary_length_ge_eleven hn h.1
  omega

theorem launchO_is_oArrival {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    cycleArrival w 1 (cycleMin_has_index_one hn h) = .oArrival := by
  obtain ⟨rest, hw⟩ := cycleMin_starts_two_odds hn h
  have hL : 1 ≤ w.length := h.1.2.2
  have hk1 : 0 + 1 < w.length := cycleMin_has_index_one hn h
  have h0 : w[0]'(Nat.lt_of_succ_lt hk1) = Branch.odd := by
    subst hw
    simp
  exact odd_run_terminates_oArrival hL hk1 h0

/-- First sure `E` follows `O^{a₁}` with `a₁ ≥ 2`, so the arrival is
    `oArrival` by `odd_run_terminates_oArrival`. -/
theorem cycleMin_firstE_follows_odd_run {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    ∃ a v, 2 ≤ a ∧ w = oddEvenBlock a 1 ++ v :=
  cycleMin_run_form_first_block hn h

/-- Schema / bunched-fill index of the third sure `E`. A general
    CycleMin third even need not be E-arrival (three-valley leftover). -/
def assembleFill_thirdEIndex (f : NecklaceFill) : ℕ :=
  4 + f.a1Extras + f.middleOdds + f.extraEvens

theorem assembleFill_thirdE_lt (f : NecklaceFill) :
    assembleFill_thirdEIndex f < (assembleFill f).length := by
  simp [assembleFill_thirdEIndex, assembleFill]
  omega

/-- Concrete bunched fill `OOEEEE`: third sure `E` is E-arrival. -/
theorem assembleFill_empty_thirdE_eArrival :
    cycleArrival (assembleFill ⟨0, 0, 0, 0⟩) 4 (by decide) = .eArrival := by
  decide +kernel

/-! ## Stem kinds (not the cartoon `OO?E`) -/

inductive StemKind
  | empty
  | capture
  | descent
  | join (arr : CycleArrival)
  deriving DecidableEq, Repr

/-- Default painted stem: one unknown-color `0+` slot. Never sure `OOE`. -/
def defaultStemSlots : List BeadSlot :=
  [BeadSlot.intervalUnknown .zeroPlus]

/-- Optional launching overlay. Last bead is *not* a sure `E`. -/
def optionalLaunchStemSlots : List BeadSlot :=
  [BeadSlot.sureOdd, BeadSlot.sureOdd, BeadSlot.intervalUnknown .zeroPlus]

theorem stem_slots_not_cycle_schema :
    defaultStemSlots ≠ balloonSchema.map BalloonStation.asSlot ∧
      optionalLaunchStemSlots ≠ balloonSchema.map BalloonStation.asSlot := by
  decide

theorem defaultStem_not_sure_OOE :
    defaultStemSlots ≠
      [BeadSlot.sureOdd, BeadSlot.sureOdd, BeadSlot.sureEven] := by
  decide

theorem stemKind_not_balloonSchema :
    defaultStemSlots ≠ balloonSchema.map BalloonStation.asSlot :=
  stem_slots_not_cycle_schema.1

/-! ## Optional realized witness -/

inductive WitnessFate
  | compiledCycle
  | leftover
  | capture
  deriving DecidableEq, Repr

structure RealizedWitness where
  n : ℕ
  word : List Branch
  fate : WitnessFate
  joinIndex : ℕ
  stemParent : Option ℕ
  deriving Repr

structure IdealLollipop where
  cycle : CycleFigure := {}
  stem : StemKind := .empty
  join : JoinFigure := ⟨.valley⟩
  witness : Option RealizedWitness := none
  deriving Repr

def schematicLollipop : IdealLollipop := {}

theorem schematicLollipop_empty_stem : schematicLollipop.stem = .empty :=
  rfl

theorem schematicLollipop_no_witness : schematicLollipop.witness = none :=
  rfl

theorem schematicLollipop_join_valley :
    schematicLollipop.join.site = .valley :=
  rfl

/-- The only compiled cycle witness. Not a nontrivial CycleMin. -/
def compiledCycleWitness : RealizedWitness where
  n := 1
  word := [.odd]
  fate := .compiledCycle
  joinIndex := 0
  stemParent := none

theorem compiledCycleWitness_is_cycle :
    CycleMin compiledCycleWitness.n compiledCycleWitness.word :=
  cycleMin_one_odd

theorem compiledCycleWitness_is_one : compiledCycleWitness.n = 1 :=
  rfl

theorem empty_stem_on_sink : OnOrbit 1 1 [.odd] :=
  ⟨cycleMin_one_odd.1, 0, by decide, rfl⟩

/-! ## Stem inhabitants -/

theorem even_tower_three_to_one :
    follows (2 ^ (2 ^ 2)) (List.replicate 3 Branch.even) ∧
      image (2 ^ (2 ^ 2)) (List.replicate 3 Branch.even) = 1 :=
  even_tower_to_one (k := 3) (by decide)

def evenTowerThree_witness : RealizedWitness where
  n := 16
  word := List.replicate 3 Branch.even
  fate := .capture
  joinIndex := 0
  stemParent := some 2

theorem evenTowerThree_n : evenTowerThree_witness.n = 2 ^ (2 ^ 2) :=
  rfl

theorem evenTowerThree_capture :
    follows evenTowerThree_witness.n evenTowerThree_witness.word ∧
      image evenTowerThree_witness.n evenTowerThree_witness.word = 1 := by
  simpa [evenTowerThree_witness] using even_tower_three_to_one

theorem stem_descent_two : FiniteProgress 2 :=
  even_finiteProgress (by decide) (by decide)

def itineraryWalkOf3 : List Branch :=
  [.odd, .odd, .odd, .even, .even, .even]

theorem walkOf3_follows : follows 3 itineraryWalkOf3 :=
  (followsB_iff 3 itineraryWalkOf3).mp (by decide +kernel)

theorem walkOf3_image : image 3 itineraryWalkOf3 = 1 := by
  decide +kernel

theorem walkOf3_reachesOne : ReachesOne 3 :=
  capture_reachesOne walkOf3_follows walkOf3_image

def walkOf3_witness : RealizedWitness where
  n := 3
  word := itineraryWalkOf3
  fate := .capture
  joinIndex := 0
  stemParent := some 2

theorem walkOf3_not_cycleMin : ¬ CycleMin 3 itineraryWalkOf3 := by
  intro h
  have := cycle_itinerary_length_ge_eleven (by decide : (2 : ℕ) ≤ 3) h.1
  simp [itineraryWalkOf3] at this

/-- O-arrival join ending `E`: the sink fork `2 → 1 ← 1`. Previous
    letter of `[.odd]` is `O`, so arrival is `oArrival` and the stem
    is even (`oArrival_stem_even`). -/
def sink_collision_two_to_one : CollisionFactorization where
  start := 1
  word := [.odd]
  index := 0
  stemParent := 2
  hCycle := cycleMin_one_odd.1
  hIndex := by decide
  hStemEdge := floorPower_two
  hStemOff := by
    intro hon
    obtain ⟨_, k, hk, hk1⟩ := hon
    have : k = 0 := Nat.lt_one_iff.mp (by simpa using hk)
    subst this
    exact (by decide : ¬(1 : ℕ) = 2) hk1

theorem sink_collision_is_oArrival :
    sink_collision_two_to_one.arrival = .oArrival := by
  decide +kernel

theorem sink_collision_stem_even :
    sink_collision_two_to_one.stemParent % 2 = 0 :=
  oArrival_collision_stem_even sink_collision_two_to_one
    sink_collision_is_oArrival

theorem sink_seam_is_oArrival_join :
    joinArrival [.odd] 0 (by decide) = Branch.odd := by
  simp [joinArrival, predIndex]

/-- Valley / E-arrival stem terminal is unknown. `{1}` cannot E-arrive
    (`cycleItinerary_one_not_eArrival`). An E-arrival odd-stem witness
    is already a nontrivial CycleMin
    (`eArrival_odd_stem_has_nontrivial_cycleMin`). -/
theorem valley_stem_terminal_unknown {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    stemTerminalOf (cycleArrival w 0
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h.1.2.2)) = .unknown := by
  rw [valley_is_eArrival hn h]
  rfl

def leftoverO7EEEE_witness : RealizedWitness where
  n := 0
  word := itineraryO7EEEE
  fate := .leftover
  joinIndex := 0
  stemParent := none

theorem leftoverO7EEEE_witness_shape :
    CycleMinShape leftoverO7EEEE_witness.word :=
  leftover_O7EEEE_inhabits_shape

theorem leftoverO7EEEE_witness_not_cycle {m : ℕ} :
    ¬ CycleItinerary m leftoverO7EEEE_witness.word :=
  leftover_O7EEEE_not_cycle

theorem necklace_pin_misses_off_shape :
    ¬ CycleMinShape necklacePinMiss2005 ∧
      ¬ CycleMinShape necklacePinMiss3004 :=
  necklace_pin_misses_not_CycleMinShape

/-- Banner: the figure does not claim a nontrivial cycle. `{1}` is the
    only compiled `CycleMin`. This is not a halt theorem. -/
theorem figure_compiled_cycle_is_sink :
    compiledCycleWitness.n = 1 ∧
      CycleMin 1 compiledCycleWitness.word ∧
        schematicLollipop.witness = none :=
  ⟨rfl, cycleMin_one_odd, rfl⟩

end Problems.Juggler
