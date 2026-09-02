import Problems.Juggler.PrefixTwoEven
import Problems.Juggler.PrefixBunchedEval

namespace Problems.Juggler

/-!
# Last three-even bunched leftover after an arbitrary CycleMin prefix

Generalizes the seven bunched `CycleItinerary` exclusions to
`CycleMin n (u ++ family)`. Large `y = T_u(n)` uses the existing
family tail at `y`. Below the family cutoff, a start that follows
the leftover never returns into `[2, y]`. Not a bunched-short
attack, not Z5, and not a halt theorem.
-/

theorem threeEvenEEE_length (a : ℕ) : (threeEvenEEE a).length = a + 3 := by
  simp [threeEvenEEE, List.length_append, List.length_replicate]

theorem threeEvenEOEE_length (a : ℕ) : (threeEvenEOEE a).length = a + 4 := by
  simp [threeEvenEOEE, List.length_append, List.length_replicate]

theorem threeEvenEEOE_length (a : ℕ) : (threeEvenEEOE a).length = a + 4 := by
  simp [threeEvenEEOE, List.length_append, List.length_replicate]

theorem threeEvenEOOEE_length (a : ℕ) : (threeEvenEOOEE a).length = a + 5 := by
  simp [threeEvenEOOEE, List.length_append, List.length_replicate]

theorem threeEvenEOEOE_length (a : ℕ) : (threeEvenEOEOE a).length = a + 5 := by
  simp [threeEvenEOEOE, List.length_append, List.length_replicate]

theorem threeEvenEOOOEE_length (a : ℕ) : (threeEvenEOOOEE a).length = a + 6 := by
  simp [threeEvenEOOOEE, List.length_append, List.length_replicate]

theorem threeEvenEOOEOE_length (a : ℕ) : (threeEvenEOOEOE a).length = a + 6 := by
  simp [threeEvenEOOEOE, List.length_append, List.length_replicate]

theorem prefix_odd_run_seven_odds {n a : ℕ} {u v : List Branch}
    (ha : 7 ≤ a)
    (h : follows (image n u) (List.replicate a Branch.odd ++ v)) :
    follows (image n u) sevenOdds := by
  have hO : follows (image n u) (List.replicate a Branch.odd) :=
    follows_of_append_left h
  have hsplit : List.replicate a Branch.odd =
      sevenOdds ++ List.replicate (a - 7) Branch.odd := by
    have hsum : 7 + (a - 7) = a := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (a - 7) Branch.odd)
    (by simpa [hsplit] using hO)

/-! ## EEE -/

theorem prefix_eee_preimage {n a : ℕ} {u : List Branch}
    (_ha : 6 ≤ a) (hy : 1 ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEEE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (n + 1) ^ (2 ^ (a + 3)) := by
  set y := image n u
  set v := u ++ List.replicate a Branch.odd
  have hsplit : u ++ threeEvenEEE a = v ++ List.replicate 3 Branch.even := by
    simp [threeEvenEEE, v, List.append_assoc]
  have hC : CycleItinerary n (v ++ List.replicate 3 Branch.even) := by
    simpa [hsplit] using h
  have hz := cycle_trailing_evens_lt (r := 3) (by decide) hC
  have hO : follows y (List.replicate a Branch.odd) :=
    follows_of_append_left (v := List.replicate 3 Branch.even)
      (follows_of_append_right (u := u) (by simpa [threeEvenEEE] using h.1))
  have hpow := odd_run_lower_growth hy hO
  have himg : image y (List.replicate a Branch.odd) = image n v := by
    simp [y, v, image_append]
  have hz' : image y (List.replicate a Branch.odd) < (n + 1) ^ 8 := by
    simpa [himg] using hz
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow :
      image y (List.replicate a Branch.odd) ^ (2 ^ a) <
        (n + 1) ^ (2 ^ (a + 3)) := by
    have := pow_lt_of_lt_pow_mul (k := 8) (m := 2 ^ a) hz' hm
    rwa [eight_mul_two_pow a] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eee_of_y {n a : ℕ} {u : List Branch}
    (ha : 6 ≤ a) (h : CycleMin n (u ++ threeEvenEEE a))
    (hy : 128 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEEE a).length := by
    have : (threeEvenEEE a).length = a + 3 := threeEvenEEE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 128) hy
  have hcell := prefix_eee_preimage ha hy1 hC
  have htail := three_even_eee_tail (n := y) hy ha
  have hle : (n + 1) ^ (2 ^ (a + 3)) ≤ (y + 1) ^ (2 ^ (a + 3)) :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _
  have hlt : y ^ (3 ^ a) <
      2 ^ denomBits a * (y + 1) ^ (2 ^ (a + 3)) :=
    lt_of_lt_of_le hcell (Nat.mul_le_mul_left _ hle)
  exact (not_lt_of_gt htail) hlt

theorem no_cycleMin_prefix_eee_of_lt {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 6 ≤ a) (h : CycleMin n (u ++ threeEvenEEE a))
    (hylt : image n u < 256) : False := by
  set y := image n u
  have hlen : 1 ≤ (threeEvenEEE a).length := by
    have : (threeEvenEEE a).length = a + 3 := threeEvenEEE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ y := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB y (threeEvenEEE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h6 | hge
  · subst h6
    have hfalse := returnsIntoB_ooooooeee_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryOOOOOOEEE = true := by
      simpa [threeEvenEEE_of_six] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · exact no_follows_seven_odds_of_lt256 hy2 hylt
      (prefix_odd_run_seven_odds hge
        (follows_of_append_right (u := u) (by simpa [threeEvenEEE] using hC.1)))

theorem no_cycleMin_prefix_eee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 6 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEEE a) := by
  intro h
  cases lt_or_ge (image n u) 256 with
  | inl hlt => exact no_cycleMin_prefix_eee_of_lt hn ha h hlt
  | inr hge =>
      exact no_cycleMin_prefix_eee_of_y ha h
        (le_trans (by decide : (128 : ℕ) ≤ 256) hge)

/-! ## EOEE -/

theorem prefix_eoee_z_lt {n a : ℕ} {u : List Branch}
    (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOEE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 6 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  have hsplit : u ++ threeEvenEOEE a =
      (u ++ List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOEE, List.append_assoc]
  have hC : CycleItinerary n
      ((u ++ List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image Y (List.replicate a Branch.odd)
  set y := image Y (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.even, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEOEE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y [Branch.odd] :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 1) hy1 hyO
  have hpimg :
      image n (u ++ List.replicate a Branch.odd ++ [Branch.even, Branch.odd]) =
        floorPower y := by
    simp [Y, y, image_append, image]
  have hle' : y ^ 3 ≤ 4 * floorPower y ^ 2 := by
    simpa [denomBits_one] using hpow
  have hp' : floorPower y < (n + 1) ^ 4 := by
    rwa [hpimg] at hp
  have hpY : floorPower y < (Y + 1) ^ 4 :=
    lt_of_lt_of_le hp' (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _)
  have hplt : 4 * floorPower y ^ 2 < 4 * (Y + 1) ^ 8 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 2) hpY (by decide)
    exact Nat.mul_lt_mul_of_pos_left this (by decide : (0 : ℕ) < 4)
  have hy3 : y ^ 3 < (Y + 1) ^ 9 :=
    lt_of_le_of_lt hle' (hplt.trans (four_mul_succ_pow8_lt_succ_pow9 hY))
  have h9 : (Y + 1) ^ 9 = ((Y + 1) ^ 3) ^ 3 := by
    rw [← Nat.pow_mul]
  have hylt : y < (Y + 1) ^ 3 :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h9 ▸ hy3)
  have hys : y + 1 ≤ (Y + 1) ^ 3 := Nat.succ_le_of_lt hylt
  have : (y + 1) ^ 2 ≤ ((Y + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hys 2
  have hexp : ((Y + 1) ^ 3) ^ 2 = (Y + 1) ^ 6 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hzlt (hexp ▸ this)

theorem prefix_eoee_preimage {n a : ℕ} {u : List Branch}
    (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOEE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (6 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  have hz := prefix_eoee_z_lt hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOEE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 6) ^ (2 ^ a) = (Y + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 6 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (6 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eoee_of_y_five {n : ℕ} {u : List Branch}
    (h : CycleMin n (u ++ threeEvenEOEE 5))
    (hy : 314 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOEE 5).length := by
    have : (threeEvenEOEE 5).length = 9 := threeEvenEOEE_length 5
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY4 : 4 ≤ y := le_trans (by decide : (4 : ℕ) ≤ 314) hy
  have hcell := prefix_eoee_preimage hY4 hyn hC
  have htail := three_even_eoee_tail_of_five (n := y) hy (by decide : (5 : ℕ) ≤ 5)
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eoee_of_y_six {n a : ℕ} {u : List Branch}
    (ha : 6 ≤ a) (h : CycleMin n (u ++ threeEvenEOEE a))
    (hy : 16 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOEE a).length := by
    have : (threeEvenEOEE a).length = a + 4 := threeEvenEOEE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY4 : 4 ≤ y := le_trans (by decide : (4 : ℕ) ≤ 16) hy
  have hcell := prefix_eoee_preimage hY4 hyn hC
  have htail := three_even_eoee_tail_of_six (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eoee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOEE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEOEE a).length := by
    have : (threeEvenEOEE a).length = a + 4 := threeEvenEOEE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEOEE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a = 5 ∨ a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h5 | h6 | hge
  · subst h5
    cases lt_or_ge (image n u) 314 with
    | inl hlt =>
        have hfalse := returnsIntoB_ooooo_eoee_lt314 ⟨image n u, hlt⟩ hy2
        have htrue' : returnsIntoB (image n u) itineraryOOOOOEOEE = true := by
          simpa [threeEvenEOEE_of_five] using htrue
        rw [hfalse] at htrue'
        exact Bool.false_ne_true htrue'
    | inr hge => exact no_cycleMin_prefix_eoee_of_y_five h hge
  · subst h6
    cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hfalse := returnsIntoB_oooooo_eoee_lt256 ⟨image n u, hlt⟩ hy2
        have htrue' : returnsIntoB (image n u) itineraryOOOOOOEOEE = true := by
          simpa [threeEvenEOEE_of_six] using htrue
        rw [hfalse] at htrue'
        exact Bool.false_ne_true htrue'
    | inr hge =>
        exact no_cycleMin_prefix_eoee_of_y_six (by decide) h
          (le_trans (by decide : (16 : ℕ) ≤ 256) hge)
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEOEE] using hC.1)))
    | inr hgeY =>
        exact no_cycleMin_prefix_eoee_of_y_six
          (le_trans (by decide : (6 : ℕ) ≤ 7) hge) h
          (le_trans (by decide : (16 : ℕ) ≤ 256) hgeY)

/-! ## EEOE -/

theorem prefix_eeoe_z_lt {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEEOE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 6 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  set pref := u ++ List.replicate a Branch.odd ++ [Branch.even]
  have hsplit : u ++ threeEvenEEOE a =
      pref ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEEOE, pref, List.append_assoc]
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  set z := image Y (List.replicate a Branch.odd)
  set s := image Y (List.replicate a Branch.odd ++ [Branch.even])
  set y := image n (pref ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have hf : follows z
      [Branch.even, Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEEOE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hseq : s = floorPower z := by
    simp [s, z, image_append, image]
  have hzlt : z < (s + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hseq.symm).2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    simpa [s, hseq, image] using hf.2
  have he2 : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, Y, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he2).mp hyeq.symm).2
  have hys : s + 1 ≤ (y + 1) ^ 2 := Nat.succ_le_of_lt hslt
  have hz4 : z < (y + 1) ^ 4 := by
    have : (s + 1) ^ 2 ≤ ((y + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hys 2
    have hexp : ((y + 1) ^ 2) ^ 2 = (y + 1) ^ 4 := by rw [← Nat.pow_mul]
    exact lt_of_lt_of_le hzlt (hexp ▸ this)
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have hysuccY : (y + 1) ^ 3 < 2 * (Y + 1) ^ 4 :=
    lt_of_lt_of_le hysucc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _))
  exact lt_of_lt_of_le hz4
    (le_of_lt (two_mul_succ_cube_lt_succ_pow6 hY hysuccY))

theorem prefix_eeoe_preimage {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEEOE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (6 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  have hz := prefix_eeoe_z_lt hn hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.even, Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEEOE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 6) ^ (2 ^ a) = (Y + 1) ^ (6 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 6 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (6 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eeoe_of_y_five {n : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (u ++ threeEvenEEOE 5))
    (hy : 314 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEEOE 5).length := by
    have : (threeEvenEEOE 5).length = 9 := threeEvenEEOE_length 5
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY4 : 4 ≤ y := le_trans (by decide : (4 : ℕ) ≤ 314) hy
  have hcell := prefix_eeoe_preimage hn hY4 hyn hC
  have htail := three_even_eoee_tail_of_five (n := y) hy (by decide : (5 : ℕ) ≤ 5)
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eeoe_of_y_six {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 6 ≤ a) (h : CycleMin n (u ++ threeEvenEEOE a))
    (hy : 16 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEEOE a).length := by
    have : (threeEvenEEOE a).length = a + 4 := threeEvenEEOE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY4 : 4 ≤ y := le_trans (by decide : (4 : ℕ) ≤ 16) hy
  have hcell := prefix_eeoe_preimage hn hY4 hyn hC
  have htail := three_even_eoee_tail_of_six (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eeoe {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 5 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEEOE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEEOE a).length := by
    have : (threeEvenEEOE a).length = a + 4 := threeEvenEEOE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEEOE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a = 5 ∨ a = 6 ∨ 7 ≤ a := by omega
  rcases hcases with h5 | h6 | hge
  · subst h5
    cases lt_or_ge (image n u) 314 with
    | inl hlt =>
        have hfalse := returnsIntoB_ooooo_eeoe_lt314 ⟨image n u, hlt⟩ hy2
        have htrue' : returnsIntoB (image n u) itineraryOOOOOEEOE = true := by
          simpa [threeEvenEEOE_of_five] using htrue
        rw [hfalse] at htrue'
        exact Bool.false_ne_true htrue'
    | inr hge => exact no_cycleMin_prefix_eeoe_of_y_five hn h hge
  · subst h6
    cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hfalse := returnsIntoB_oooooo_eeoe_lt256 ⟨image n u, hlt⟩ hy2
        have htrue' : returnsIntoB (image n u) itineraryOOOOOOEEOE = true := by
          simpa [threeEvenEEOE_of_six] using htrue
        rw [hfalse] at htrue'
        exact Bool.false_ne_true htrue'
    | inr hge =>
        exact no_cycleMin_prefix_eeoe_of_y_six hn (by decide) h
          (le_trans (by decide : (16 : ℕ) ≤ 256) hge)
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEEOE] using hC.1)))
    | inr hgeY =>
        exact no_cycleMin_prefix_eeoe_of_y_six hn
          (le_trans (by decide : (6 : ℕ) ≤ 7) hge) h
          (le_trans (by decide : (16 : ℕ) ≤ 256) hgeY)

/-! ## EOOEE -/

theorem prefix_eooee_z_lt {n a : ℕ} {u : List Branch}
    (hY : 32 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOEE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 4 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 32) hY
  have hsplit : u ++ threeEvenEOOEE a =
      (u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOEE, List.append_assoc]
  have hC : CycleItinerary n
      ((u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image Y (List.replicate a Branch.odd)
  set y := image Y (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEOOEE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 2) hy1 hyO
  have hpimg :
      image n (u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd]) =
        image y (List.replicate 2 Branch.odd) := by
    simp [Y, y, image_append, image]
  have hle' : y ^ 9 ≤ 1024 * image y (List.replicate 2 Branch.odd) ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten] using hpow
  have hp' : image y (List.replicate 2 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hpY : image y (List.replicate 2 Branch.odd) < (Y + 1) ^ 4 :=
    lt_of_lt_of_le hp' (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _)
  have hplt : 1024 * image y (List.replicate 2 Branch.odd) ^ 4 <
      1024 * (Y + 1) ^ 16 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 4) hpY (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (by decide : (0 : ℕ) < 1024)
  have hy9 : y ^ 9 < (Y + 1) ^ 18 :=
    lt_of_le_of_lt hle' (hplt.trans (two_pow10_succ_pow16_lt_succ_pow18 hY))
  have h18 : (Y + 1) ^ 18 = ((Y + 1) ^ 2) ^ 9 := by
    rw [← Nat.pow_mul]
  have hylt : y < (Y + 1) ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : (9 : ℕ) ≠ 0)).mp (h18 ▸ hy9)
  have hys : y + 1 ≤ (Y + 1) ^ 2 := Nat.succ_le_of_lt hylt
  have : (y + 1) ^ 2 ≤ ((Y + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hys 2
  have hexp : ((Y + 1) ^ 2) ^ 2 = (Y + 1) ^ 4 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hzlt (hexp ▸ this)

theorem prefix_eooee_preimage {n a : ℕ} {u : List Branch}
    (hY : 32 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOEE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (4 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 32) hY
  have hz := prefix_eooee_z_lt hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOOEE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 4) ^ (2 ^ a) = (Y + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 4 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (4 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eooee_of_y {n a : ℕ} {u : List Branch}
    (ha : 4 ≤ a) (h : CycleMin n (u ++ threeEvenEOOEE a))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOOEE a).length := by
    have : (threeEvenEOOEE a).length = a + 5 := threeEvenEOOEE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY32 : 32 ≤ y := le_trans (by decide : (32 : ℕ) ≤ 256) hy
  have hcell := prefix_eooee_preimage hY32 hyn hC
  have htail := three_even_eooee_tail (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eooee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 4 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOOEE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEOOEE a).length := by
    have : (threeEvenEOOEE a).length = a + 5 := threeEvenEOOEE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEOOEE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
  rcases hcases with hle | hge
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hA : a - 4 < 3 := by omega
        have hfalse :
            returnsIntoB (image n u) (threeEvenEOOEE (a - 4 + 4)) = false :=
          returnsIntoB_eooee_lt256 ⟨image n u, hlt⟩ ⟨a - 4, hA⟩ hy2
        have haeq : a - 4 + 4 = a := by omega
        have hfalse' : returnsIntoB (image n u) (threeEvenEOOEE a) = false := by
          simpa [haeq] using hfalse
        rw [hfalse'] at htrue
        exact Bool.false_ne_true htrue
    | inr hgeY => exact no_cycleMin_prefix_eooee_of_y ha h hgeY
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEOOEE] using hC.1)))
    | inr hgeY => exact no_cycleMin_prefix_eooee_of_y ha h hgeY

/-! ## EOEOE -/

theorem prefix_eoeoe_z_lt {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 32 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOEOE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 4 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 32) hY
  set pref := u ++ List.replicate a Branch.odd ++ [Branch.even, Branch.odd]
  have hsplit : u ++ threeEvenEOEOE a =
      pref ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEOEOE, pref, List.append_assoc]
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  set z := image Y (List.replicate a Branch.odd)
  set w := image Y (List.replicate a Branch.odd ++ [Branch.even])
  set s := image Y (List.replicate a Branch.odd ++ [Branch.even, Branch.odd])
  set y := image n (pref ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have hf : follows z
      [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEOEOE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hweq : w = floorPower z := by
    simp [w, z, image_append, image]
  have hzlt : z < (w + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hweq.symm).2
  have hwO : follows w (List.replicate 1 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [w, hweq, image, List.replicate] using hf.2)
  have hw1 : 1 ≤ w := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [w, hweq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := w) (a := 1) hw1 hwO
  have hseq : s = image w (List.replicate 1 Branch.odd) := by
    simp [s, w, image_append, image]
  have hle' : w ^ 3 ≤ 4 * s ^ 2 := by
    simpa [denomBits_one, hseq] using hpow
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have hf1 : follows w
        [Branch.odd, Branch.even, Branch.odd, Branch.even] := by
      simpa [w, hweq, image] using hf.2
    simpa [s, hseq, image, List.replicate] using hf1.2
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, Y, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hs4 : s ^ 2 < (y + 1) ^ 4 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 2) hslt (by decide)
  have hplt : 4 * s ^ 2 < 4 * (y + 1) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 4)
  have hw3 : w ^ 3 < 4 * (y + 1) ^ 4 := lt_of_le_of_lt hle' hplt
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have hysuccY : (y + 1) ^ 3 < 2 * (Y + 1) ^ 4 :=
    lt_of_lt_of_le hysucc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _))
  have h8 : 8 * (y + 1) < (Y + 1) ^ 2 :=
    eight_mul_succ_lt_succ_sq hY hysuccY
  have hy4 : (y + 1) ^ 4 = (y + 1) * (y + 1) ^ 3 :=
    (pow_succ (y + 1) 3).trans (mul_comm _ _)
  have h4y : 4 * (y + 1) ^ 4 < (Y + 1) ^ 6 := by
    have hmid : 4 * (y + 1) * (y + 1) ^ 3 <
        4 * (y + 1) * (2 * (Y + 1) ^ 4) :=
      Nat.mul_lt_mul_of_pos_left hysuccY
        (Nat.mul_pos (by decide : (0 : ℕ) < 4) (Nat.succ_pos y))
    have hexp : 4 * (y + 1) * (2 * (Y + 1) ^ 4) =
        8 * (y + 1) * (Y + 1) ^ 4 := by ring
    have hfin : 8 * (y + 1) * (Y + 1) ^ 4 < (Y + 1) ^ 6 := by
      have hr : (Y + 1) ^ 6 = (Y + 1) ^ 2 * (Y + 1) ^ 4 := by
        rw [← Nat.pow_add]
      rw [hr]
      exact Nat.mul_lt_mul_of_pos_right h8 (pow_pos (Nat.succ_pos Y) 4)
    have h4y' : 4 * (y + 1) ^ 4 = 4 * (y + 1) * (y + 1) ^ 3 := by
      rw [hy4, mul_assoc]
    exact h4y' ▸ (hmid.trans_eq hexp).trans hfin
  have hw6 : w ^ 3 < (Y + 1) ^ 6 := hw3.trans h4y
  have h6 : (Y + 1) ^ 6 = ((Y + 1) ^ 2) ^ 3 := by rw [← Nat.pow_mul]
  have hwlt : w < (Y + 1) ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : (3 : ℕ) ≠ 0)).mp (h6 ▸ hw6)
  have hws : w + 1 ≤ (Y + 1) ^ 2 := Nat.succ_le_of_lt hwlt
  have : (w + 1) ^ 2 ≤ ((Y + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hws 2
  have hexp : ((Y + 1) ^ 2) ^ 2 = (Y + 1) ^ 4 := by rw [← Nat.pow_mul]
  exact lt_of_lt_of_le hzlt (hexp ▸ this)

theorem prefix_eoeoe_preimage {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 32 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOEOE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (4 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 32) hY
  have hz := prefix_eoeoe_z_lt hn hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.even, Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOEOE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 4) ^ (2 ^ a) = (Y + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 4 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (4 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eoeoe_of_y {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 4 ≤ a) (h : CycleMin n (u ++ threeEvenEOEOE a))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOEOE a).length := by
    have : (threeEvenEOEOE a).length = a + 5 := threeEvenEOEOE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY32 : 32 ≤ y := le_trans (by decide : (32 : ℕ) ≤ 256) hy
  have hcell := prefix_eoeoe_preimage hn hY32 hyn hC
  have htail := three_even_eooee_tail (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eoeoe {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 4 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOEOE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEOEOE a).length := by
    have : (threeEvenEOEOE a).length = a + 5 := threeEvenEOEOE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEOEOE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
  rcases hcases with hle | hge
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hA : a - 4 < 3 := by omega
        have hfalse :
            returnsIntoB (image n u) (threeEvenEOEOE (a - 4 + 4)) = false :=
          returnsIntoB_eoeoe_lt256 ⟨image n u, hlt⟩ ⟨a - 4, hA⟩ hy2
        have haeq : a - 4 + 4 = a := by omega
        have hfalse' : returnsIntoB (image n u) (threeEvenEOEOE a) = false := by
          simpa [haeq] using hfalse
        rw [hfalse'] at htrue
        exact Bool.false_ne_true htrue
    | inr hgeY => exact no_cycleMin_prefix_eoeoe_of_y hn ha h hgeY
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEOEOE] using hC.1)))
    | inr hgeY => exact no_cycleMin_prefix_eoeoe_of_y hn ha h hgeY

/-! ## EOOOEE -/

set_option exponentiation.threshold 64

theorem prefix_eoooee_z_lt {n a : ℕ} {u : List Branch}
    (hY : 3 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOOEE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 4 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 3) hY
  have hsplit : u ++ threeEvenEOOOEE a =
      (u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOOEE, List.append_assoc]
  have hC : CycleItinerary n
      ((u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC
  set z := image Y (List.replicate a Branch.odd)
  set y := image Y (List.replicate a Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEOOOEE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hyO : follows y (List.replicate 3 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := y) (a := 3) hy1 hyO
  have hpimg :
      image n (u ++ List.replicate a Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) =
        image y (List.replicate 3 Branch.odd) := by
    simp [Y, y, image_append, image]
  have hle' : y ^ 27 ≤ 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 := by
    simpa [denomBits_three, three_pow_three] using hpow
  have hp' : image y (List.replicate 3 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hpY : image y (List.replicate 3 Branch.odd) < (Y + 1) ^ 4 :=
    lt_of_lt_of_le hp' (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _)
  have hplt : 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 <
      2 ^ 38 * (Y + 1) ^ 32 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 8) hpY (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (pow_pos (by decide : (0 : ℕ) < 2) 38)
  have hy27 : y ^ 27 < 2 ^ 38 * (Y + 1) ^ 32 := lt_of_le_of_lt hle' hplt
  exact z_lt_succ_pow4_of_y hzlt (y_lt_succ_sq_of_odd27 hY hy27)

theorem prefix_eoooee_preimage {n a : ℕ} {u : List Branch}
    (hY : 3 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOOEE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (4 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 3) hY
  have hz := prefix_eoooee_z_lt hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOOOEE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 4) ^ (2 ^ a) = (Y + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 4 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (4 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eoooee_of_y_four {n a : ℕ} {u : List Branch}
    (ha : 4 ≤ a) (h : CycleMin n (u ++ threeEvenEOOOEE a))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOOOEE a).length := by
    have : (threeEvenEOOOEE a).length = a + 6 := threeEvenEOOOEE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY3 : 3 ≤ y := le_trans (by decide : (3 : ℕ) ≤ 256) hy
  have hcell := prefix_eoooee_preimage hY3 hyn hC
  have htail := three_even_eooee_tail (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eoooee_of_y_three {n : ℕ} {u : List Branch}
    (h : CycleMin n (u ++ threeEvenEOOOEE 3))
    (hy : 256 ≤ image n u) : False := by
  set Y := image n u
  have hC := cycleMin_cycleItinerary h
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hn197 : 197 ≤ Y := le_trans (by decide : (197 : ℕ) ≤ 256) hy
  have hn24 : 24 ≤ Y := le_trans (by decide : (24 : ℕ) ≤ 256) hy
  have hlen : 1 ≤ (threeEvenEOOOEE 3).length := by
    have : (threeEvenEOOOEE 3).length = 9 := threeEvenEOOOEE_length 3
    omega
  have hyn : n ≤ Y := cycleMin_prefix_y_ge hlen h
  set z := image Y (List.replicate 3 Branch.odd)
  set y := image Y (List.replicate 3 Branch.odd ++ [Branch.even])
  have hyeq : y = floorPower z := by
    simp [y, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate 3 Branch.odd)
      (by simpa [threeEvenEOOOEE, List.append_assoc] using hC.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq.symm).2
  have hO : follows Y (List.replicate 3 Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.odd,
        Branch.even, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOOOEE] using hC.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hz8 : z ^ 8 < (y + 1) ^ 16 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 8) hzlt (by decide)
  have h27 : Y ^ 27 < 2 ^ 38 * (y + 1) ^ 16 := by
    have hle : Y ^ 27 ≤ 2 ^ 38 * z ^ 8 := by
      simpa [denomBits_three, three_pow_three, z] using hpow
    exact lt_of_le_of_lt hle
      (Nat.mul_lt_mul_of_pos_left hz8
        (pow_pos (by decide : (0 : ℕ) < 2) 38))
  have hsplit : u ++ threeEvenEOOOEE 3 =
      (u ++ List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even := by
    simp [threeEvenEOOOEE, List.append_assoc]
  have hC' : CycleItinerary n
      ((u ++ List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) ++
        List.replicate 2 Branch.even) := by
    simpa [hsplit] using hC
  have hp := cycle_trailing_evens_lt (r := 2) (by decide) hC'
  have hyO : follows y (List.replicate 3 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.even])
      (by simpa [y, hyeq, image, List.replicate] using hf.2)
  have hy1 : 1 ≤ y := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [y, hyeq] using floorPower_pos hz1
  have hpowy := odd_run_lower_growth (n := y) (a := 3) hy1 hyO
  have hpimg :
      image n (u ++ List.replicate 3 Branch.odd ++
        [Branch.even, Branch.odd, Branch.odd, Branch.odd]) =
        image y (List.replicate 3 Branch.odd) := by
    simp [Y, y, image_append, image]
  have hle' : y ^ 27 ≤ 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 := by
    simpa [denomBits_three, three_pow_three] using hpowy
  have hp' : image y (List.replicate 3 Branch.odd) < (n + 1) ^ 4 := by
    rwa [← hpimg]
  have hpY : image y (List.replicate 3 Branch.odd) < (Y + 1) ^ 4 :=
    lt_of_lt_of_le hp' (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _)
  have hplt : 2 ^ 38 * image y (List.replicate 3 Branch.odd) ^ 8 <
      2 ^ 38 * (Y + 1) ^ 32 := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 8) hpY (by decide)
    exact Nat.mul_lt_mul_of_pos_left this
      (pow_pos (by decide : (0 : ℕ) < 2) 38)
  have hy27 : y ^ 27 < 2 ^ 38 * (Y + 1) ^ 32 := lt_of_le_of_lt hle' hplt
  cases lt_or_ge y 39 with
  | inl hlt => exact eoooee_small_y_false hn24 hlt h27
  | inr hge => exact eoooee_large_y_false hn197 hge hy27 h27

theorem no_cycleMin_prefix_eoooee {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 3 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOOOEE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEOOOEE a).length := by
    have : (threeEvenEOOOEE a).length = a + 6 := threeEvenEOOOEE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEOOOEE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
  rcases hcases with hle | hge
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hA : a - 3 < 4 := by omega
        have hfalse :
            returnsIntoB (image n u) (threeEvenEOOOEE (a - 3 + 3)) = false :=
          returnsIntoB_eoooee_lt256 ⟨image n u, hlt⟩ ⟨a - 3, hA⟩ hy2
        have haeq : a - 3 + 3 = a := by omega
        have hfalse' : returnsIntoB (image n u) (threeEvenEOOOEE a) = false := by
          simpa [haeq] using hfalse
        rw [hfalse'] at htrue
        exact Bool.false_ne_true htrue
    | inr hgeY =>
        have hsplit : a = 3 ∨ 4 ≤ a := by omega
        rcases hsplit with h3 | h4
        · subst h3
          exact no_cycleMin_prefix_eoooee_of_y_three h hgeY
        · exact no_cycleMin_prefix_eoooee_of_y_four h4 h hgeY
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEOOOEE] using hC.1)))
    | inr hgeY =>
        exact no_cycleMin_prefix_eoooee_of_y_four
          (le_trans (by decide : (4 : ℕ) ≤ 7) hge) h hgeY

/-! ## EOOEOE -/

theorem prefix_eooeoe_z_lt {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOEOE a)) :
    image (image n u) (List.replicate a Branch.odd) <
      (image n u + 1) ^ 4 := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  set pref :=
    u ++ List.replicate a Branch.odd ++ [Branch.even, Branch.odd, Branch.odd]
  have hsplit : u ++ threeEvenEOOEOE a =
      pref ++ [Branch.even, Branch.odd, Branch.even] := by
    simp [threeEvenEOOEOE, pref, List.append_assoc]
  have hC : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [hsplit] using h
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC
  set z := image Y (List.replicate a Branch.odd)
  set uimg := image Y (List.replicate a Branch.odd ++ [Branch.even])
  set s := image n pref
  set y := image n (pref ++ [Branch.even])
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate a Branch.odd)
      (by simpa [threeEvenEOOEOE, List.append_assoc] using h.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hueq : uimg = floorPower z := by
    simp [uimg, z, image_append, image]
  have hzlt : z < (uimg + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hueq.symm).2
  have huO : follows uimg (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [uimg, hueq, image, List.replicate] using hf.2)
  have hu1 : 1 ≤ uimg := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [uimg, hueq] using floorPower_pos hz1
  have hpow := odd_run_lower_growth (n := uimg) (a := 2) hu1 huO
  have hseq : s = image uimg (List.replicate 2 Branch.odd) := by
    simp [s, uimg, pref, Y, image_append, image]
  have hle' : uimg ^ 9 ≤ 1024 * s ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten, hseq] using hpow
  have hf1 : follows uimg
      [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.even] := by
    simpa [uimg, hueq, image] using hf.2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := List.replicate 2 Branch.odd) hf1
    simpa [s, hseq, image, List.replicate] using this
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hs4 : s ^ 4 < (y + 1) ^ 8 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 4) hslt (by decide)
  have hu9 : uimg ^ 9 < 1024 * (y + 1) ^ 8 :=
    lt_of_le_of_lt hle'
      (Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 1024))
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have hysuccY : (y + 1) ^ 3 < 2 * (Y + 1) ^ 4 :=
    lt_of_lt_of_le hysucc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _))
  exact z_lt_succ_pow4_of_y hzlt (eooeoe_u_lt_succ_sq hY hu9 hysuccY)

theorem prefix_eooeoe_preimage {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hY : 4 ≤ image n u) (hyn : n ≤ image n u)
    (h : CycleItinerary n (u ++ threeEvenEOOEOE a)) :
    image n u ^ (3 ^ a) <
      2 ^ denomBits a * (image n u + 1) ^ (4 * 2 ^ a) := by
  set Y := image n u
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 4) hY
  have hz := prefix_eooeoe_z_lt hn hY hyn h
  have hO : follows Y (List.replicate a Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOOEOE] using h.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hZ : ((Y + 1) ^ 4) ^ (2 ^ a) = (Y + 1) ^ (4 * 2 ^ a) :=
    (Nat.pow_mul (Y + 1) 4 (2 ^ a)).symm
  have hm : 2 ^ a ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : image Y (List.replicate a Branch.odd) ^ (2 ^ a) <
      (Y + 1) ^ (4 * 2 ^ a) := by
    have := Nat.pow_lt_pow_left hz hm
    rwa [hZ] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_eooeoe_of_y_four {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 4 ≤ a) (h : CycleMin n (u ++ threeEvenEOOEOE a))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC := cycleMin_cycleItinerary h
  have hlen : 1 ≤ (threeEvenEOOEOE a).length := by
    have : (threeEvenEOOEOE a).length = a + 6 := threeEvenEOOEOE_length a
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hY4 : 4 ≤ y := le_trans (by decide : (4 : ℕ) ≤ 256) hy
  have hcell := prefix_eooeoe_preimage hn hY4 hyn hC
  have htail := three_even_eooee_tail (n := y) hy ha
  exact (not_lt_of_gt htail) hcell

theorem no_cycleMin_prefix_eooeoe_of_y_three {n : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n (u ++ threeEvenEOOEOE 3))
    (hy : 256 ≤ image n u) : False := by
  set Y := image n u
  have hC := cycleMin_cycleItinerary h
  have hY1 : 1 ≤ Y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hn197 : 197 ≤ Y := le_trans (by decide : (197 : ℕ) ≤ 256) hy
  have hn24 : 24 ≤ Y := le_trans (by decide : (24 : ℕ) ≤ 256) hy
  have hlen : 1 ≤ (threeEvenEOOEOE 3).length := by
    have : (threeEvenEOOEOE 3).length = 9 := threeEvenEOOEOE_length 3
    omega
  have hyn : n ≤ Y := cycleMin_prefix_y_ge hlen h
  set z := image Y (List.replicate 3 Branch.odd)
  set uimg := image Y (List.replicate 3 Branch.odd ++ [Branch.even])
  set pref :=
    u ++ List.replicate 3 Branch.odd ++ [Branch.even, Branch.odd, Branch.odd]
  set s := image n pref
  set y := image n (pref ++ [Branch.even])
  have hueq : uimg = floorPower z := by
    simp [uimg, z, image_append, image]
  have hf : follows z
      [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := u ++ List.replicate 3 Branch.odd)
      (by simpa [threeEvenEOOEOE, List.append_assoc] using hC.1)
    simpa [z, Y, image_append] using this
  have he : z % 2 = 0 := hf.1
  have hzlt : z < (uimg + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hueq.symm).2
  have hO : follows Y (List.replicate 3 Branch.odd) :=
    follows_of_append_left
      (v := [Branch.even, Branch.odd, Branch.odd, Branch.even,
        Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [threeEvenEOOEOE] using hC.1))
  have hpow := odd_run_lower_growth hY1 hO
  have hz8 : z ^ 8 < (uimg + 1) ^ 16 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 8) hzlt (by decide)
  have h27 : Y ^ 27 < 2 ^ 38 * (uimg + 1) ^ 16 := by
    have hle : Y ^ 27 ≤ 2 ^ 38 * z ^ 8 := by
      simpa [denomBits_three, three_pow_three, z] using hpow
    exact lt_of_le_of_lt hle
      (Nat.mul_lt_mul_of_pos_left hz8
        (pow_pos (by decide : (0 : ℕ) < 2) 38))
  have hC' : CycleItinerary n
      (pref ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [threeEvenEOOEOE, pref, List.append_assoc] using hC
  have hy3 := cycle_eoe_suffix_y_cube_lt (u := pref) hC'
  have hy3' : y ^ 3 < (n + 1) ^ 4 := by
    simpa [y, pref] using hy3
  have huO : follows uimg (List.replicate 2 Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (by simpa [uimg, hueq, image, List.replicate] using hf.2)
  have hu1 : 1 ≤ uimg := by
    have hz1 : 1 ≤ z := image_pos hY1 _
    simpa [uimg, hueq] using floorPower_pos hz1
  have hpowu := odd_run_lower_growth (n := uimg) (a := 2) hu1 huO
  have hseq : s = image uimg (List.replicate 2 Branch.odd) := by
    simp [s, uimg, pref, Y, image_append, image]
  have hle' : uimg ^ 9 ≤ 1024 * s ^ 4 := by
    simpa [denomBits_two, three_pow_two, two_pow_ten, hseq] using hpowu
  have hf1 : follows uimg
      [Branch.odd, Branch.odd, Branch.even, Branch.odd, Branch.even] := by
    simpa [uimg, hueq, image] using hf.2
  have hf2 : follows s [Branch.even, Branch.odd, Branch.even] := by
    have := follows_of_append_right (u := List.replicate 2 Branch.odd) hf1
    simpa [s, hseq, image, List.replicate] using this
  have hes : s % 2 = 0 := hf2.1
  have hyeq : y = floorPower s := by
    simp [y, s, pref, image_append, image]
  have hslt : s < (y + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval hes).mp hyeq.symm).2
  have hs4 : s ^ 4 < (y + 1) ^ 8 :=
    pow_lt_of_lt_pow_mul (k := 2) (m := 4) hslt (by decide)
  have hu9 : uimg ^ 9 < 1024 * (y + 1) ^ 8 :=
    lt_of_le_of_lt hle'
      (Nat.mul_lt_mul_of_pos_left hs4 (by decide : (0 : ℕ) < 1024))
  have hA : 3 ≤ n + 1 := by omega
  have hysucc : (y + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hy3'
  have hysuccY : (y + 1) ^ 3 < 2 * (Y + 1) ^ 4 :=
    lt_of_lt_of_le hysucc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _))
  have hu27 : uimg ^ 27 < 2 ^ 38 * (Y + 1) ^ 32 :=
    eooeoe_u_pow27 hu9 hysuccY
  cases lt_or_ge uimg 39 with
  | inl hlt => exact eoooee_small_y_false hn24 hlt h27
  | inr hge => exact eoooee_large_y_false hn197 hge hu27 h27

theorem no_cycleMin_prefix_eooeoe {n a : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (ha : 3 ≤ a) :
    ¬CycleMin n (u ++ threeEvenEOOEOE a) := by
  intro h
  have hlen : 1 ≤ (threeEvenEOOEOE a).length := by
    have : (threeEvenEOOEOE a).length = a + 6 := threeEvenEOOEOE_length a
    omega
  have hyn : n ≤ image n u := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ image n u := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB (image n u) (threeEvenEOOEOE a) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : a ≤ 6 ∨ 7 ≤ a := by omega
  rcases hcases with hle | hge
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        have hA : a - 3 < 4 := by omega
        have hfalse :
            returnsIntoB (image n u) (threeEvenEOOEOE (a - 3 + 3)) = false :=
          returnsIntoB_eooeoe_lt256 ⟨image n u, hlt⟩ ⟨a - 3, hA⟩ hy2
        have haeq : a - 3 + 3 = a := by omega
        have hfalse' : returnsIntoB (image n u) (threeEvenEOOEOE a) = false := by
          simpa [haeq] using hfalse
        rw [hfalse'] at htrue
        exact Bool.false_ne_true htrue
    | inr hgeY =>
        have hsplit : a = 3 ∨ 4 ≤ a := by omega
        rcases hsplit with h3 | h4
        · subst h3
          exact no_cycleMin_prefix_eooeoe_of_y_three hn h hgeY
        · exact no_cycleMin_prefix_eooeoe_of_y_four hn h4 h hgeY
  · cases lt_or_ge (image n u) 256 with
    | inl hlt =>
        exact no_follows_seven_odds_of_lt256 hy2 hlt
          (prefix_odd_run_seven_odds hge
            (follows_of_append_right (u := u)
              (by simpa [threeEvenEOOEOE] using hC.1)))
    | inr hgeY =>
        exact no_cycleMin_prefix_eooeoe_of_y_four hn
          (le_trans (by decide : (4 : ℕ) ≤ 7) hge) h hgeY

end Problems.Juggler
