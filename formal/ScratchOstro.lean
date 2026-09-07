import Problems.Juggler.OstrowskiSandwich
open Problems.Juggler

set_option maxHeartbeats 4000000 in
theorem window_scan_kernel_try :
    ((List.range' 50508 251486).all fun L =>
      decide (greedyDigitSum L ≤ 37)) = true := by
  decide +kernel
