import Problems.Juggler.LeftoverFamilies
import Problems.Juggler.PrefixTwoEvenEval

namespace Problems.Juggler

/-!
# Last two-even leftover after an arbitrary CycleMin prefix

Generalizes `no_cycleMin_gapped_three_even_ee` / `_eoe` from the
first-E prefix `O^a E` to any prefix `u`. Large `y = T_u(n)` is the
shared two-even tail at `y`. Below 256, a start that follows the
leftover never returns into `[2, y]`. Not a bunched-short attack,
not Z5, not a length-11 assembler, and not a halt theorem.
-/

theorem twoEvenEE_length {k : ℕ} (hk : 2 ≤ k) : (twoEvenEE k).length = k := by
  have : k - 2 + 2 = k := by omega
  simpa [twoEvenEE, List.length_append, List.length_replicate] using this

theorem twoEvenEOE_length {k : ℕ} (hk : 3 ≤ k) : (twoEvenEOE k).length = k := by
  have : k - 3 + 3 = k := by omega
  simpa [twoEvenEOE, List.length_append, List.length_replicate] using this

theorem cycleMin_prefix_y_ge {n : ℕ} {u v : List Branch}
    (hv : 1 ≤ v.length) (h : CycleMin n (u ++ v)) :
    n ≤ image n u := by
  have hlen : u.length < (u ++ v).length := by
    simp [List.length_append]
    omega
  have : n ≤ floorPower^[u.length] n := cycleMin_ge h hlen
  simpa [image_eq_iterate] using this

theorem returnsIntoB_iff {y : ℕ} {w : List Branch} :
    returnsIntoB y w = true ↔
      follows y w ∧ 2 ≤ image y w ∧ image y w ≤ y := by
  simp [returnsIntoB, followsB_iff, Bool.and_eq_true]
  exact and_assoc

theorem returnsIntoB_of_cycleMin_suffix {n : ℕ} {u v : List Branch}
    (hn : 2 ≤ n) (hv : 1 ≤ v.length) (h : CycleMin n (u ++ v)) :
    returnsIntoB (image n u) v = true := by
  have hC := cycleMin_cycleItinerary h
  have hy := cycleMin_prefix_y_ge hv h
  have hf : follows (image n u) v := follows_of_append_right hC.1
  have himg : image (image n u) v = n := by
    simpa [image_append] using hC.2.1
  refine returnsIntoB_iff.mpr ⟨hf, ?_, ?_⟩
  · simpa [himg] using hn
  · simpa [himg] using hy

theorem prefix_two_even_ee_preimage {n k : ℕ} {u : List Branch}
    (hk : 6 ≤ k) (hy : 1 ≤ image n u)
    (h : CycleItinerary n (u ++ twoEvenEE k)) :
    image n u ^ (3 ^ (k - 2)) <
      2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k) := by
  set y := image n u
  set v := u ++ List.replicate (k - 2) Branch.odd
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hsplit : u ++ twoEvenEE k = v ++ List.replicate 2 Branch.even := by
    simp [twoEvenEE, v, List.append_assoc]
  have hC : CycleItinerary n (v ++ List.replicate 2 Branch.even) := by
    simpa [hsplit] using h
  have hz := cycle_trailing_evens_lt (r := 2) (by decide) hC
  have hO : follows y (List.replicate (k - 2) Branch.odd) :=
    follows_of_append_left (v := List.replicate 2 Branch.even)
      (follows_of_append_right (u := u) (by simpa [twoEvenEE] using h.1))
  have hpow := odd_run_lower_growth hy hO
  have himg : image y (List.replicate (k - 2) Branch.odd) = image n v := by
    simp [y, v, image_append]
  have hz' : image y (List.replicate (k - 2) Branch.odd) < (n + 1) ^ 4 := by
    simpa [himg] using hz
  have hm : 2 ^ (k - 2) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow :
      image y (List.replicate (k - 2) Branch.odd) ^ (2 ^ (k - 2)) <
        (n + 1) ^ (2 ^ k) := by
    have := pow_lt_of_lt_pow_mul (k := 4) (m := 2 ^ (k - 2)) hz' hm
    rwa [four_mul_two_pow_sub hk2] at this
  exact lt_of_le_of_lt hpow
    (Nat.mul_lt_mul_of_pos_left hzpow
      (pow_pos (by decide : (0 : ℕ) < 2) _))

theorem no_cycleMin_prefix_two_even_ee_of_y {n k : ℕ} {u : List Branch}
    (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEE k))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC : CycleItinerary n (u ++ twoEvenEE k) := cycleMin_cycleItinerary h
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEE k).length := by
    have : (twoEvenEE k).length = k := twoEvenEE_length hk2
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hcell := prefix_two_even_ee_preimage hk hy1 hC
  have htail := shared_two_even_tail (n := y) hy hk
  have hle : (n + 1) ^ (2 ^ k) ≤ (y + 1) ^ (2 ^ k) :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _
  have hlt : y ^ (3 ^ (k - 2)) <
      2 ^ denomBits (k - 2) * (y + 1) ^ (2 ^ k) :=
    lt_of_lt_of_le hcell (Nat.mul_le_mul_left _ hle)
  exact (not_lt_of_gt htail) hlt

theorem no_cycleMin_prefix_two_even_ee_of_eq {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEE k))
    (hy : image n u = n) : False := by
  have hC := cycleMin_cycleItinerary h
  have hf : follows n (twoEvenEE k) := by
    simpa [hy] using follows_of_append_right (u := u) hC.1
  have himg : image n (twoEvenEE k) = n := by
    have : image (image n u) (twoEvenEE k) = n := by
      simpa [image_append] using hC.2.1
    simpa [hy] using this
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEE k).length := by
    have : (twoEvenEE k).length = k := twoEvenEE_length hk2
    omega
  exact no_cycle_itinerary_two_even_ee hn hk ⟨hf, himg, hlen⟩

theorem prefix_two_even_ee_follows_seven_odds {n k : ℕ} {u : List Branch}
    (hk : 9 ≤ k) (h : CycleItinerary n (u ++ twoEvenEE k)) :
    follows (image n u) sevenOdds := by
  have hO : follows (image n u) (List.replicate (k - 2) Branch.odd) :=
    follows_of_append_left (v := List.replicate 2 Branch.even)
      (follows_of_append_right (u := u) (by simpa [twoEvenEE] using h.1))
  have hsplit : List.replicate (k - 2) Branch.odd =
      sevenOdds ++ List.replicate (k - 9) Branch.odd := by
    have hsum : 7 + (k - 9) = k - 2 := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (k - 9) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycleMin_prefix_two_even_ee_of_lt {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEE k))
    (hylt : image n u < 256) : False := by
  set y := image n u
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEE k).length := by
    have : (twoEvenEE k).length = k := twoEvenEE_length hk2
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ y := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB y (twoEvenEE k) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k := by omega
  rcases hcases with h6 | h7 | h8 | hge
  · subst h6
    have hfalse := returnsIntoB_ooooee_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryOOOOEE = true := by
      simpa [twoEvenEE_of_six] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · subst h7
    have hfalse := returnsIntoB_oooooee_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryOOOOOEE = true := by
      simpa [twoEvenEE_of_seven] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · subst h8
    have hfalse := returnsIntoB_two_even_ee8_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryTwoEvenEE8 = true := by
      simpa [twoEvenEE_of_eight] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · exact no_follows_seven_odds_of_lt256 hy2 hylt
      (prefix_two_even_ee_follows_seven_odds hge hC)

theorem no_cycleMin_prefix_two_even_ee {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) :
    ¬CycleMin n (u ++ twoEvenEE k) := by
  intro h
  cases lt_or_ge (image n u) 256 with
  | inl hlt => exact no_cycleMin_prefix_two_even_ee_of_lt hn hk h hlt
  | inr hge => exact no_cycleMin_prefix_two_even_ee_of_y hk h hge

theorem prefix_two_even_eoe_preimage {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (hy : 1 ≤ image n u)
    (h : CycleItinerary n (u ++ twoEvenEOE k)) :
    image n u ^ (3 ^ (k - 2)) <
      2 ^ denomBits (k - 2) * (n + 1) ^ (2 ^ k) := by
  set y := image n u
  set odds := List.replicate (k - 3) Branch.odd
  set z := image y odds
  set w := image y (odds ++ [Branch.even])
  have hk3 : 3 ≤ k := le_trans (by decide : (3 : ℕ) ≤ 6) hk
  have hk2 : 2 ≤ k := le_trans (by decide : (2 : ℕ) ≤ 6) hk
  have hC' : CycleItinerary n
      ((u ++ odds) ++ [Branch.even, Branch.odd, Branch.even]) := by
    simpa [twoEvenEOE, List.append_assoc] using h
  have hO : follows y odds :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [twoEvenEOE] using h.1))
  have he : z % 2 = 0 := by
    have hf : follows y (odds ++ [Branch.even, Branch.odd, Branch.even]) :=
      follows_of_append_right (u := u)
        (by simpa [twoEvenEOE, List.append_assoc] using h.1)
    have hfE : follows z [Branch.even, Branch.odd, Branch.even] :=
      follows_of_append_right (u := odds) hf
    change z % 2 = 0 ∧ follows (floorPower z) [Branch.odd, Branch.even] at hfE
    exact hfE.1
  have hyeq : floorPower z = w := by
    simp [z, w, odds, image_append, image]
  have hzlt : z < (w + 1) ^ 2 :=
    ((floorPower_even_eq_iff_sq_interval he).mp hyeq).2
  have hpow := odd_run_lower_growth hy hO
  have hm : 2 ^ (k - 3) ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
  have hzpow : z ^ (2 ^ (k - 3)) < (w + 1) ^ (2 ^ (k - 2)) := by
    have := pow_lt_of_lt_pow_mul (k := 2) (m := 2 ^ (k - 3)) hzlt hm
    have hexp : 2 * 2 ^ (k - 3) = 2 ^ (k - 2) := by
      rw [two_mul_two_pow]
      congr 1
      omega
    rwa [hexp] at this
  have hmid : y ^ (3 ^ (k - 3)) <
      2 ^ denomBits (k - 3) * (w + 1) ^ (2 ^ (k - 2)) :=
    lt_of_le_of_lt hpow
      (Nat.mul_lt_mul_of_pos_left hzpow
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  have hcube : y ^ (3 ^ (k - 2)) <
      2 ^ (3 * denomBits (k - 3)) * (w + 1) ^ (3 * 2 ^ (k - 2)) := by
    have hlt : (y ^ (3 ^ (k - 3))) ^ 3 <
        (2 ^ denomBits (k - 3) * (w + 1) ^ (2 ^ (k - 2))) ^ 3 :=
      Nat.pow_lt_pow_left hmid (by decide : (3 : ℕ) ≠ 0)
    have hL : (y ^ (3 ^ (k - 3))) ^ 3 = y ^ (3 ^ (k - 2)) := by
      rw [← Nat.pow_mul, three_pow_succ_sub hk3]
    have hR : (2 ^ denomBits (k - 3) * (w + 1) ^ (2 ^ (k - 2))) ^ 3 =
        2 ^ (3 * denomBits (k - 3)) * (w + 1) ^ (3 * 2 ^ (k - 2)) :=
      two_mul_pow_cube _ _ _
    rwa [hL, hR] at hlt
  have hw3 : w ^ 3 < (n + 1) ^ 4 := by
    have hcube' := cycle_eoe_suffix_y_cube_lt (u := u ++ odds) hC'
    simpa [w, y, odds, image_append, List.append_assoc] using hcube'
  have hA : 3 ≤ n + 1 := by omega
  have hwsucc : (w + 1) ^ 3 < 2 * (n + 1) ^ 4 :=
    cube_succ_lt_two_mul_of_cube_lt_pow4 hA hw3
  have hwraise : (w + 1) ^ (3 * 2 ^ (k - 2)) <
      2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k) := by
    have hm' : 2 ^ (k - 2) ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (pow_pos (by decide : (0 : ℕ) < 2) _)
    have hlt : ((w + 1) ^ 3) ^ (2 ^ (k - 2)) <
        (2 * (n + 1) ^ 4) ^ (2 ^ (k - 2)) :=
      Nat.pow_lt_pow_left hwsucc hm'
    have hL : ((w + 1) ^ 3) ^ (2 ^ (k - 2)) =
        (w + 1) ^ (3 * 2 ^ (k - 2)) :=
      (Nat.pow_mul (w + 1) 3 (2 ^ (k - 2))).symm
    have hR : (2 * (n + 1) ^ 4) ^ (2 ^ (k - 2)) =
        2 ^ (2 ^ (k - 2)) * (n + 1) ^ (4 * 2 ^ (k - 2)) := by
      rw [mul_pow, Nat.pow_mul]
    rw [hL, hR, four_mul_two_pow_sub hk2] at hlt
    exact hlt
  have hmid' : y ^ (3 ^ (k - 2)) <
      2 ^ (3 * denomBits (k - 3)) *
        (2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k)) :=
    lt_trans hcube
      (Nat.mul_lt_mul_of_pos_left hwraise
        (pow_pos (by decide : (0 : ℕ) < 2) _))
  have hexp :
      2 ^ (3 * denomBits (k - 3)) *
          (2 ^ (2 ^ (k - 2)) * (n + 1) ^ (2 ^ k)) =
        2 ^ (3 * denomBits (k - 3) + 2 ^ (k - 2)) * (n + 1) ^ (2 ^ k) := by
    rw [← mul_assoc, ← Nat.pow_add]
  have hbits : 3 * denomBits (k - 3) + 2 ^ (k - 2) = denomBits (k - 2) := by
    have : k - 2 = (k - 3) + 1 := by omega
    rw [this, denomBits_succ]
  rwa [hexp, hbits] at hmid'

theorem no_cycleMin_prefix_two_even_eoe_of_y {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEOE k))
    (hy : 256 ≤ image n u) : False := by
  set y := image n u
  have hC : CycleItinerary n (u ++ twoEvenEOE k) := cycleMin_cycleItinerary h
  have hk3 : 3 ≤ k := le_trans (by decide : (3 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEOE k).length := by
    have : (twoEvenEOE k).length = k := twoEvenEOE_length hk3
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 256) hy
  have hcell := prefix_two_even_eoe_preimage hn hk hy1 hC
  have htail := shared_two_even_tail (n := y) hy hk
  have hle : (n + 1) ^ (2 ^ k) ≤ (y + 1) ^ (2 ^ k) :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hyn) _
  have hlt : y ^ (3 ^ (k - 2)) <
      2 ^ denomBits (k - 2) * (y + 1) ^ (2 ^ k) :=
    lt_of_lt_of_le hcell (Nat.mul_le_mul_left _ hle)
  exact (not_lt_of_gt htail) hlt

theorem no_cycleMin_prefix_two_even_eoe_of_eq {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEOE k))
    (hy : image n u = n) : False := by
  have hC := cycleMin_cycleItinerary h
  have hf : follows n (twoEvenEOE k) := by
    simpa [hy] using follows_of_append_right (u := u) hC.1
  have himg : image n (twoEvenEOE k) = n := by
    have : image (image n u) (twoEvenEOE k) = n := by
      simpa [image_append] using hC.2.1
    simpa [hy] using this
  have hk3 : 3 ≤ k := le_trans (by decide : (3 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEOE k).length := by
    have : (twoEvenEOE k).length = k := twoEvenEOE_length hk3
    omega
  exact no_cycle_itinerary_two_even_eoe hn hk ⟨hf, himg, hlen⟩

theorem prefix_two_even_eoe_follows_seven_odds {n k : ℕ} {u : List Branch}
    (hk : 10 ≤ k) (h : CycleItinerary n (u ++ twoEvenEOE k)) :
    follows (image n u) sevenOdds := by
  have hO : follows (image n u) (List.replicate (k - 3) Branch.odd) :=
    follows_of_append_left (v := [Branch.even, Branch.odd, Branch.even])
      (follows_of_append_right (u := u) (by simpa [twoEvenEOE] using h.1))
  have hsplit : List.replicate (k - 3) Branch.odd =
      sevenOdds ++ List.replicate (k - 10) Branch.odd := by
    have hsum : 7 + (k - 10) = k - 3 := by omega
    rw [sevenOdds, ← List.replicate_add, hsum]
  exact follows_of_append_left (v := List.replicate (k - 10) Branch.odd)
    (by simpa [hsplit] using hO)

theorem no_cycleMin_prefix_two_even_eoe_of_lt {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) (h : CycleMin n (u ++ twoEvenEOE k))
    (hylt : image n u < 256) : False := by
  set y := image n u
  have hk3 : 3 ≤ k := le_trans (by decide : (3 : ℕ) ≤ 6) hk
  have hlen : 1 ≤ (twoEvenEOE k).length := by
    have : (twoEvenEOE k).length = k := twoEvenEOE_length hk3
    omega
  have hyn : n ≤ y := cycleMin_prefix_y_ge hlen h
  have hy2 : 2 ≤ y := le_trans hn hyn
  have hC := cycleMin_cycleItinerary h
  have htrue : returnsIntoB y (twoEvenEOE k) = true :=
    returnsIntoB_of_cycleMin_suffix hn hlen h
  have hcases : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ 10 ≤ k := by omega
  rcases hcases with h6 | h7 | h8 | h9 | hge
  · subst h6
    have hfalse := returnsIntoB_oooeoe_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryOOOEOE' = true := by
      simpa [twoEvenEOE_of_six, itineraryOOOEOE_eq_eval] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · subst h7
    have hfalse := returnsIntoB_ooooeoe_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryOOOOEOE = true := by
      simpa [twoEvenEOE_of_seven] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · subst h8
    have hfalse := returnsIntoB_two_even_eoe8_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryTwoEvenEOE8 = true := by
      simpa [twoEvenEOE_of_eight] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · subst h9
    have hfalse := returnsIntoB_two_even_eoe9_lt256 ⟨y, hylt⟩ hy2
    have htrue' : returnsIntoB y itineraryTwoEvenEOE9 = true := by
      simpa [twoEvenEOE_of_nine] using htrue
    rw [hfalse] at htrue'
    exact Bool.false_ne_true htrue'
  · exact no_follows_seven_odds_of_lt256 hy2 hylt
      (prefix_two_even_eoe_follows_seven_odds hge hC)

theorem no_cycleMin_prefix_two_even_eoe {n k : ℕ} {u : List Branch}
    (hn : 2 ≤ n) (hk : 6 ≤ k) :
    ¬CycleMin n (u ++ twoEvenEOE k) := by
  intro h
  cases lt_or_ge (image n u) 256 with
  | inl hlt => exact no_cycleMin_prefix_two_even_eoe_of_lt hn hk h hlt
  | inr hge => exact no_cycleMin_prefix_two_even_eoe_of_y hn hk h hge

end Problems.Juggler
