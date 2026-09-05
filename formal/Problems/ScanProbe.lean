import Problems.Juggler
set_option maxRecDepth 4000000
open Problems.Juggler

-- how large a chunk will the kernel take?  default heartbeat limit left on.
example : ((List.range' 50508 500).all fun L =>
    decide (greedyReconstruct L = L ∧ greedyDigitSum L ≤ 37)) = true := by decide +kernel

example : ((List.range' 51008 2000).all fun L =>
    decide (greedyReconstruct L = L ∧ greedyDigitSum L ≤ 37)) = true := by decide +kernel
