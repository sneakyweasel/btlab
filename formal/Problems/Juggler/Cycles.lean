import Problems.Juggler.CycleCore
import Problems.Juggler.CycleObstructions
import Problems.Juggler.CycleExtrema

/-!
# Fixed cycle itineraries (re-export)

`CycleCore` plus named-itinerary exclusions plus `CycleExtrema`.
Existing `import Problems.Juggler.Cycles` compiles the three
layers. Declarations live in those files; this barrel does not
restate them. Leftover proofs that need a named itinerary import
`CycleObstructions`. Foundations stay on `CycleCore`.
-/
