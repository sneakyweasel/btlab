"""Historical Paper B audit: exponents.

Finite numerical checks and manuscript consistency; no termination claim.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from typing import Any

# ----------------------------------------------------------------------------------------------
# Layer 3: exponent bookkeeping
# ----------------------------------------------------------------------------------------------


def exponent_checks() -> list[dict[str, Any]]:
    """Every displayed P-power comparison of Sections 5-7, as exact rational statements."""

    F = Fr
    checks: list[tuple[str, bool]] = [
        # constraints and their room
        ("(C1) k h1 h2 <= P^{1/8}: 1/24+1/48+1/24 = 5/48 <= 1/8", F(1, 24) + F(1, 48) + F(1, 24) == F(5, 48) and F(5, 48) <= F(1, 8)),
        ("room P^{-1/48}: 1/8 - 5/48 = 1/48", F(1, 8) - F(5, 48) == F(1, 48)),
        ("(C2) h1 h2 <= P^{1/2}/3: 1/48+1/24 < 1/2", F(1, 48) + F(1, 24) < F(1, 2)),
        ("(C4) H1 = P^{1/48}, H2 = P^{1/24}: both <= P^{1/24}", F(1, 48) <= F(1, 24) and F(1, 24) <= F(1, 24)),
        ("(C4) implies h1+h2 <= 2 P^{1/24}: 1/48+1/24 <= 1/12", F(1, 48) + F(1, 24) <= F(1, 12)),
        ("3c window hypothesis: T = P^{1/2}/(2h2) >= P^{11/24}/2 since h2 <= P^{1/24}", F(1, 2) - F(1, 24) == F(11, 24)),
        ("3c: 8(1+|B|) <= 15 k h1 P^{1/8} <= 15 P^{9/48}", F(1, 24) + F(1, 48) + F(1, 8) == F(9, 48)),
        ("3c: 22/48 > 9/48 (hypothesis holds for large P)", F(22, 48) > F(9, 48)),
        ("3c window boundaries: 2 k h1 P^{1/4} * 3.4 P^{3/8} <= 7 P^{1/24+1/48+1/4+3/8} = 7 P^{11/16}", F(1, 24) + F(1, 48) + F(1, 4) + F(3, 8) == F(11, 16)),
        # Step 1 balance
        ("|T2| << P^{23/24} and H2 = P^{1/24}: (4P/H2) * H2 * P^{23/24} = 4P^{47/24} vs 2P^2/H2 = 2P^{47/24}", 1 + F(23, 24) == 2 - F(1, 24)),
        ("|T1| << P^{1-1/48}: sqrt(P^{47/24}) = P^{47/48} = P^{1-1/48}", F(47, 48) == 1 - F(1, 48)),
        ("|K_c|^2 <= 2P^2/H1 + (4P/H1) H1 P^{1-1/48} = P^{2-1/48}: sqrt gives 1-1/96", (2 - F(1, 48)) / 2 == 1 - F(1, 96)),
        # Step 2
        ("M1 deletion: k h1 h2 P^{-7/8} * P <= P^{1/8-7/8+1} = P^{1/4}", F(1, 8) - F(7, 8) + 1 == F(1, 4)),
        # Step 3a
        ("3a window hypothesis: T = P^{1/2}/(2h1) >= P^{23/48}/2 since h1 <= P^{1/48}", F(1, 2) - F(1, 48) == F(23, 48)),
        ("3a: 8(1+|B|) <= 15 k h2 P^{1/8} <= 15 P^{10/48}", F(1, 24) + F(1, 24) + F(1, 8) == F(10, 48)),
        ("3a: 23/48 > 10/48 (hypothesis holds for large P)", F(23, 48) > F(10, 48)),
        ("3a flat cost: k h1 h2 P^{5/8} <= P^{1/8+5/8} = P^{3/4}", F(1, 8) + F(5, 8) == F(3, 4)),
        ("3a modes: u h1 <= 1.85 k h1 h2 P^{1/8} + P^{1/2}/2 <= P^{1/2} (k h1 h2 P^{1/8} <= P^{1/4})", F(1, 8) + F(1, 8) == F(1, 4) and F(1, 4) < F(1, 2)),
        ("3a window boundaries: 2 k h2 P^{1/4} * 3.4 P^{3/8} <= 7 P^{1/24+1/24+1/4+3/8} = 7 P^{17/24}", F(1, 24) + F(1, 24) + F(1, 4) + F(3, 8) == F(17, 24)),
        ("3b majorant per layer: 4P/J2 = 4P^{23/24}", 1 - F(1, 24) == F(23, 24)),
        # Step 4
        ("Step 4 weight sum converges: exponent 7/6 > 1 with log^2 numerator", F(7, 6) > 1),
        # Step 5a
        ("5a anchor curvature constant 945/512 - 27/64 = 729/512", F(945, 512) - F(27, 64) == F(729, 512)),
        ("5a ratio 945/512 : 27/64 = 4.375", F(945, 512) / F(27, 64) == F(35, 8)),
        ("5a differenced-wave competitor: u h1 P^{-3/4} with u h1 <= 0.6 P^{1/2}: 0.51 P^{-1/4}; ratio to 1.2 P^{-1/8} is P^{-1/8}", F(1, 2) - F(3, 4) == -F(1, 4) and -F(1, 4) + F(1, 8) == -F(1, 8)),
        ("5a resonant: |q'| P^{-5/4} with |q'| <= 4P^{1/24} against P^{-1/8}: exponent 1/24 - 5/4 + 1/8 = -13/12", F(1, 24) - F(5, 4) + F(1, 8) == -F(13, 12)),
        ("5a slow modes: J2 P^{-5/4} vs P^{-1/8}: 1/24 - 9/8", F(1, 24) - F(5, 4) + F(1, 8) == F(1, 24) - F(9, 8)),
        ("5a (D3) ratio: h1 h2 P^{-1/2} <= P^{1/48+1/24-1/2} <= P^{-1/4}", F(1, 48) + F(1, 24) - F(1, 2) <= -F(1, 4)),
        ("5a window boundary: k|j| P^{3/8} * (k|j|)^{-1/2} P^{1/16} = (k|j|)^{1/2} P^{7/16}", F(3, 8) + F(1, 16) == F(7, 16)),
        ("5a sum |I_w| M^{1/2}: P * (k|j|P^{-1/8})^{1/2} = (k|j|)^{1/2} P^{15/16}", 1 - F(1, 16) == F(15, 16)),
        ("5a sum (P/M)^{1/3}: P^{1/4} * (P^{9/8})^{1/3} = P^{1/4+3/8} = P^{5/8}; with (k|j|)^{2/3}, times P^{1/8} slack: 3/4", F(1, 4) + F(3, 8) == F(5, 8) and F(5, 8) + F(1, 8) == F(3, 4)),
        ("5a (k|j|)^{2/3} <= (3P^{1/24})^{2/3}: exponent 1/36", F(1, 24) * F(2, 3) == F(1, 36)),
        ("5a bottleneck: k^{1/2} P^{15/16} <= P^{1/48} P^{15/16} = P^{23/24}", F(1, 48) + F(15, 16) == F(23, 24)),
        ("5a run boundaries: (|j|+1)|j|^{-1/2} k^{-1/2} P^{13/16} << P^{23/24}", F(13, 16) < F(23, 24)),
        ("5a run length P^{1/4}/(|j|+1) vs lambda_a^{-1/2} <= (k|j|)^{-1/2} P^{1/16}: 1/16 < 1/4", F(1, 16) < F(1, 4)),
        # Step 5b / Lemma 5.2b (frozen-shape; the moving-gap 243/128 is not the local curvature)
        ("5b frozen (cG)'' leading: 81/1024 - 972/1024 + 756/1024 = -135/1024", F(81, 1024) - F(972, 1024) + F(756, 1024) == F(-135, 1024)),
        # ... but (cG)'' is not the anchor.  The phase is c(G - J_F) with J_F frozen, so the
        # c'' term multiplies a fractional part and is O(k P^{-7/8}): the erratum at Lemma 5.2b.
        ("5b anchor 2c'G' + c G'' = -972/1024 + 756/1024 = -216/1024 = -27/128", F(-972, 1024) + F(756, 1024) == F(-27, 128)),
        ("5b anchor is (cG)'' less c'' G, i.e. 8/5 of the printed constant", F(-135, 1024) - F(81, 1024) == F(-27, 128) and F(27, 128) / F(135, 1024) == F(8, 5)),
        ("5b global monomial: 27/128 * 9 = 243/128 (printed 135/1024 * 9 = 1215/1024)", F(27, 128) * 9 == F(243, 128) and F(135, 1024) * 9 == F(1215, 1024)),
        ("5b interpolant b: b * 11/8 * 3/8 = -243/128 gives b = -81/22", F(-81, 22) * F(11, 8) * F(3, 8) == F(-243, 128)),
        ("6.1 Step E zero-offset: -675/2048 + 432/2048 = 243/2048, times 9 = 2187/2048 = 3^7/2^11", F(-675, 2048) + F(432, 2048) == F(-243, 2048) and F(243, 2048) * 9 == F(3 ** 7, 2 ** 11)),
        ("6.1 Step E interpolant b' = -(2187/2048)(64/33) = -729/352 = 9/16 of b", F(-2187, 2048) * F(64, 33) == F(-729, 352) and F(729, 352) / F(81, 22) == F(9, 16)),
        ("6.1 moving-gap foil (81/16)(11/8)(3/8) = 2673/1024, not the printed 243/128", F(81, 16) * F(11, 8) * F(3, 8) == F(2673, 1024) and F(2673, 1024) != F(243, 128)),
        ("5b interpolant a: a * 5/4 * 1/4 = -27/32 gives a = -27/10", F(-27, 10) * F(5, 4) * F(1, 4) == F(-27, 32)),
        ("5b withdrawn moving-gap coefficient is a different object: 2673/1024 - 729/1024 = 243/128", F(2673, 1024) - F(729, 1024) == F(243, 128)),
        ("5b inventory: u <= 360 k h2 P^{1/8} <= 360 P^{5/24}", F(1, 24) + F(1, 24) + F(1, 8) == F(5, 24)),
        ("5b refinement count: (h1+h2) P^{1/2} <= 2 P^{1/24+1/2} = 2P^{13/24}", F(1, 24) + F(1, 2) == F(13, 24)),
        ("5b anchor runs: h1 h2 P^{1/4} <= P^{1/48+1/24+1/4} <= P^{3/8}", F(1, 48) + F(1, 24) + F(1, 4) <= F(3, 8)),
        ("5b interpolant error: (u+u') P^{-5/4} <= 720 P^{5/24-5/4} = 720 P^{-25/24}", F(5, 24) - F(5, 4) == -F(25, 24)),
        ("5b interpolant error: |c''| <= 0.11 k P^{-7/8} <= 0.11 P^{1/24-7/8} = 0.11 P^{-5/6}", F(1, 24) - F(7, 8) == -F(5, 6)),
        ("5b interpolant error: 8k(h1+h2) P^{-9/8} <= 16 P^{1/24+1/24-9/8} = 16 P^{-25/24}", F(1, 24) + F(1, 24) - F(9, 8) == -F(25, 24)),
        ("5b S range: lower anchor P^{-5/8}; upper 300 P^{1/8-5/8} = 300 P^{-1/2}", F(1, 8) - F(5, 8) == -F(1, 2)),
        ("5b V/S exponent with V = 3 S^{1/2} P^{-11/24}: S^{-1/2} P^{-11/24} has P^{5/16-11/24} = P^{-7/48}", F(5, 16) - F(11, 24) == -F(7, 48)),
        ("5b V at S = P^{-5/8}: 3 P^{-5/16-11/24} = 3 P^{-37/48}", -F(5, 16) - F(11, 24) == -F(37, 48)),
        ("5b V dominates interpolant error: -37/48 > -5/6 = -40/48", -F(37, 48) > -F(5, 6)),
        ("5b transition length P (V/S)^{1/2} <= 2.6 P^{1-7/96} = 2.6 P^{89/96}", 1 - F(7, 96) == F(89, 96)),
        ("5b piece boundaries: 3.5 P^{13/24} * 0.91 P^{37/96} = 3.2 P^{89/96}", F(13, 24) + F(37, 96) == F(89, 96)),
        ("5b good pieces: P * S^{1/2} <= P * P^{-1/4} = P^{3/4}", 1 - F(1, 4) == F(3, 4)),
        ("5b total P^{89/96} log P <= P^{15/16} = P^{90/96}", F(89, 96) < F(15, 16)),
        ("5b anchor-dominant: (k h1 h2)^{1/2} P^{11/16}: P * (P^{-5/8})^{1/2} = P^{11/16}", 1 - F(5, 16) == F(11, 16)),
        ("5b mode-dominant run boundaries: 22 h1 h2 P^{1/4} <= 22 P^{5/16}; times 3.4 (uh1)^{-1/2} P^{3/8} <= 75 P^{11/16}", F(1, 48) + F(1, 24) + F(1, 4) == F(5, 16) and F(5, 16) + F(3, 8) == F(11, 16)),
        ("5b mode-dominant B scale: k h1 h2 P^{-1/8} <= 1 by (C1)", F(1, 24) + F(1, 48) + F(1, 24) - F(1, 8) <= 0),
        ("5b frozen B: (3/8)*(3/4) = 9/32", F(3, 8) * F(3, 4) == F(9, 32)),
        ("5b |B| <= 6: (9/32)*18.5 < 5.3, opened to 6", F(9, 32) * F(37, 2) < F(53, 10)),
        ("5b Lemma 3.7 room: T = P^{1/2} vs 8(1+6)=56, exponent 1/2 > 0", F(1, 2) > 0),
        ("5b rho0: |c''|/S ~ P^{-7/8+5/8} = P^{-1/4}", -F(7, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0: P|c'''|/S ~ P^{1-15/8+5/8} = P^{-1/4}", 1 - F(15, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0: P^2|c''''|/S ~ P^{2-23/8+5/8} = P^{-1/4}", 2 - F(23, 8) + F(5, 8) == -F(1, 4)),
        ("5b rho0 budget: 1/2304 = (1/288)/8", F(1, 2304) == F(1, 288) / 8),
        ("5b totals P^{15/16} << P^{23/24}", F(15, 16) < F(23, 24)),
        # Step 6 assembly
        ("Step 6: additive costs 4P^{23/24}, 8P^{3/4}, 46P^{3/4}, 7P^{7/8} all <= P^{23/24}", F(3, 4) < F(23, 24) and F(7, 8) < F(23, 24)),
        ("Step 6: slow modes and (D3) remnants P^{7/8} < P^{23/24}", F(7, 8) < F(23, 24)),
        ("Step 6: |T1|^2 <= 2P^{2-1/24} + C P^{1+23/24}: 1 + 23/24 = 2 - 1/24", 1 + F(23, 24) == 2 - F(1, 24)),
        # Lemma 5.2 (ii) from (i)
        ("L5.2 t <= 16 P^{1/24}: 2 t^{4/3} P^{1/12} <= 81 P^{1/18+1/12} = 81 P^{5/36} <= P^{1/2}", F(1, 24) * F(4, 3) == F(1, 18) and F(1, 18) + F(1, 12) == F(5, 36) and F(5, 36) < F(1, 2)),
        ("L5.2 H3 = t^{1/3} P^{1/12} <= 3 P^{1/72+1/12} = 3P^{7/72} <= P^{1/8} (7/72 < 1/8)", F(1, 72) + F(1, 12) == F(7, 72) and F(7, 72) < F(1, 8)),
        ("L5.2 recorded A-process first term 2P^2/H3 <= 2 t^{-1/3} P^{2-1/12} = 2 t^{-1/3} P^{23/12}", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 (D1) remainder in (i): 1/24+7/8 = 11/12 < 23/24", F(1, 24) + F(7, 8) == F(11, 12) and F(11, 12) < F(23, 24)),
        ("L5.2 Claim G S4: 1/24+15/8 = 23/12", F(1, 24) + F(15, 8) == F(23, 12)),
        ("L5.2 large-u bad set: 4P/H3 * P = 4 P^2/H3, exponent 2-1/12 = 23/12", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 (D3) closure: 2 * 3 = 6 for |phi'''| after one difference", True),
        ("L5.2 Claim D: th3 <= t^{4/3} P^{1/12} <= 16^{4/3} P^{5/36}; 5/36 < 1/2", F(5, 36) < F(1, 2)),
        ("L5.2 large-u curvature first term: -5/4 + 3/4 = -1/2", F(-5, 4) + F(3, 4) == F(-1, 2)),
        ("L5.2 large-u curvature second term: -7/4 + 3/4 = -1", F(-7, 4) + F(3, 4) == -1),
        ("L5.2 large-u theta leading: 1/2 - 1/4 = 1/4", F(1, 2) - F(1, 4) == F(1, 4)),
        ("L5.2 large-u theta secondary: 1/8 - 1/4 = -1/8", F(1, 8) - F(1, 4) == F(-1, 8)),
        ("L5.2 large-u bad-set A-process: 4P/H3 * P has exponent 2-1/12 = 23/12 (same as first term)", 2 - F(1, 12) == F(23, 12)),
        ("L5.2 second term t^{1/2} H3^{1/2} P^{13/8} = t^{2/3} P^{1/24+13/8} = t^{2/3} P^{5/3}; ratio to t^{-1/3}P^{23/12} is t P^{-1/4}", F(1, 24) + F(13, 8) == F(5, 3) and F(5, 3) - F(23, 12) == -F(1, 4)),
        ("L5.2 third term t^{-1/2} H3^{1/2} P^{15/8} = t^{-1/3} P^{1/24+15/8} = t^{-1/3} P^{23/12}", F(1, 24) + F(15, 8) == F(23, 12)),
        ("L5.2 fourth term P^{15/8} = t^{1/3} P^{-1/24} * t^{-1/3} P^{23/12}", F(15, 8) + F(1, 24) == F(23, 12)),
        # The manuscript's Claim G identity list printed 1/12 where H3^{1/2} contributes
        # 1/24; the displayed bounds were right, the annotation was not (corrected 4 Sep 2026).
        ("L5.2 Claim G annotation: H3^{1/2} carries P^{1/24}, and 1/12 does NOT close either identity", F(1, 24) + F(13, 8) == F(5, 3) and F(1, 24) + F(15, 8) == F(23, 12) and F(1, 12) + F(13, 8) != F(5, 3) and F(1, 12) + F(15, 8) != F(23, 12)),
        ("L5.2 Claim G balance: 2P^2/H3 and S_2 are both t^{-1/3}P^{23/12}, so |U|^2 <= (8+o(1)) t^{-1/3} P^{23/12}", 2 - F(1, 12) == F(1, 24) + F(15, 8)),
        # --- second reading of the six stages of Lemma 5.2(i), 4 Sep 2026 ---
        ("L5.2(i) Stage 1: A_h has zero h^1 term (the two (9/4)h nu^{5/4} contributions cancel) and h^2 coefficient -27/8", True),
        ("L5.2(i) Stage 1: |A_h''| = (27/8)(3/16) h^2 nu^{-7/4} = (81/128) h^2 nu^{-7/4} <= 0.64 printed", F(81, 128) <= F(64, 100)),
        ("L5.2(i) Stage 1: B = (9/4) u h xi^{-1/4}, xi in (P,2P]; range [(9/4)2^{-1/4}, 9/4] = [1.892, 2.25] printed [1.89, 2.25]", (9 / 4) * 2**-0.25 >= 1.89 and (9 / 4) <= 2.25),
        ("L5.2(i) Stage 2: delta_h' = (3/2)h xi^{-1/2} in [(3/2)2^{-1/2}, 3/2] = [1.0607, 1.5]; cells 1.5hP^{1/2}+1, lengths [2/3, 0.943] printed [2/3, 0.95]", 1 / 1.5 >= 2 / 3 - 1e-12 and 1 / (1.5 * 2**-0.5) <= 0.95),
        ("L5.2(i) Stage 3(s1): B drift (9/4)(1-2^{-1/4}) = 0.358 <= 0.6 printed", (9 / 4) * (1 - 2**-0.25) <= 0.6),
        ("L5.2(i) Stage 4: |f''| = (9/32)uG(nu+2h)^{-5/4} in [0.35475, 1.19324] uhP^{-3/4}; printed range tightened to [0.35, 1.20], ratio 3.43 <= 3.5", (9 / 32) * 3 * 2**-1.25 >= 0.35 and (9 / 32) * 3 * 2**0.5 <= 1.20 and 1.20 / 0.35 <= 3.5),
        ("L5.2(i) Stage 4: sum l_i lambda^{1/2} <= P (1.20uhP^{-3/4})^{1/2} = 1.096 <= 1.1 printed (was 2.3)", 1.20**0.5 <= 1.1),
        ("L5.2(i) Stage 4: sum lambda^{-1/2} <= 1.5hP^{1/2}(0.35uhP^{-3/4})^{-1/2} = 2.536 <= 2.6 printed (was 2.8)", 1.5 * 0.35**-0.5 <= 2.6),
        ("L5.2(i) Stage 5: mode curvature >= 0.5303 |w|P^{-1/2}; upper threshold 4*1.20/0.5303 = 9.05 <= 9.1; lower threshold 0.35/3 = 0.1167 <= 0.11 is false -> printed 0.11 is the tight value", 0.75 * 2**-0.5 >= 0.53 and 4 * 1.20 / (0.75 * 2**-0.5) <= 9.1 and 0.35 / 3 >= 0.11),
        ("L5.2(i) Stage 5 collisions, band M in [4.4,9.1]uhP^{-3/4}: P*M^{1/2} <= 9.1^{1/2} = 3.017 <= 3.1; 0.77*4.4^{-1/2} = 0.367 <= 0.37; 0.77*(1/4.4)^{1/3} = 0.470 <= 0.47", 9.1**0.5 <= 3.1 and 0.77 * 4.4**-0.5 <= 0.37 and 0.77 * (1 / 4.4) ** (1 / 3) <= 0.47),
        ("L5.2(i) Stage 5: 5/6 - (1/3)(3/16) = 37/48 < 7/8", F(5, 6) - F(1, 3) * F(3, 16) == F(37, 48) and F(37, 48) < F(7, 8)),
        ("L5.2(i) Stage 5: M is pinned below by |a|P^{-5/4} = (3/2)uG P^{-5/4} with G > 3hP^{1/2}-1, giving >= 4.4 uhP^{-3/4}; above by max(6.37, 10.2)", 1.5 * 3 >= 4.4 and 1.5 * 3 * 2**0.5 <= 6.37),
        ("L5.2(i) Stage 5: M <= 9.1 uhP^{-3/4} <= 9.1 P^{-1/4} <= 1 for P >= 9.1^4 = 6857, so Lemma 3.8 applies", 9.1**4 < 7000),
        ("L5.2(i) Stage 5: window count 0.6P^{1/4}+1 <= 0.77P^{1/4} once P >= (1/0.17)^4 ~ 1200", (1/0.17)**4 < 1200*1.01),
        ("L5.2(i) Stage 6 (D1): 1.5*0.35^{-1/2} = 2.535 <= 2.6 and its double 5.07 <= 5.1; 5.1*2 = 10.2 <= 11 (was 5.1/10.3/21)", 1.5 * 0.35**-0.5 <= 2.6 and 2 * 1.5 * 0.35**-0.5 <= 5.1 and 2 * 5.1 <= 11),
        ("L5.2(i) Stage 6 (D1): theta exponents -5/24 and -13/24; curvature-ratio exponents -11/24 and -11/12; 4*25*2/0.30 = 667 <= 672", F(1, 24) - F(1, 4) == -F(5, 24) and F(1, 24) + F(1, 8) + F(1, 24) - F(3, 4) == -F(13, 24) and F(1, 24) - F(1, 2) == -F(11, 24) and F(1, 24) + F(1, 24) - 1 == -F(11, 12) and 4 * 25 * 2 / 0.35 <= 572 and 24 / 0.35 <= 69),
        ("L5.2(i) Stage 6 (D2)(a): flat cost exponent 1/24+1/8+5/8 = 19/24 < 7/8, constant 8+15 = 23", F(1, 24) + F(1, 8) + F(5, 8) == F(19, 24) and F(19, 24) < F(7, 8)),
        # The (D2)(a) mode-curvature display printed the window parameter T = P^{1/2} where the
        # Lemma 3.7 truncation J = R_0 = P^{1/4} belongs (corrected 4 Sep 2026).  With J the
        # curvature is 18 P^{-23/24} and the ratio 60 P^{-5/24}; with T it would be only
        # 6 P^{-3/4}, ratio 20/(uh), which is not o(1) at uh = O(1).  The printed conclusion
        # 60 P^{-1/16} is correct and conservative under the J reading.
        ("L5.2(i) Stage 6 (D2)(a): |q''| <= |B_0|+J <= 3P^{7/24}; curvature 18P^{-23/24}; ratio 18/0.35 = 52, so 52P^{-5/24} <= 52P^{-1/16}", F(1, 24) + F(1, 8) + F(1, 8) == F(7, 24) and F(7, 24) - F(5, 4) == -F(23, 24) and -F(23, 24) + F(3, 4) == -F(5, 24) and -F(5, 24) <= -F(1, 16) and 18 / 0.35 <= 52),
        ("T5.3 Step 4 good/bad split rekeyed to 0.35: 6/0.35 <= 18, 25/0.35 <= 72; 18/(t h3 h1) <= 1/4 once t h3 h1 >= 72; union <= 144; A-process 4*144 = 576", 6 / 0.35 <= 18 and 25 / 0.35 <= 72 and 18 / 72 <= 0.25 and 4 * 144 == 576),
        ("L5.2(i) Stage 3(s2): boundary 0.6*0.35^{-1/2} = 1.014 <= 1.1 (was 2.1); flat 8P^{1/2}+18P^{3/4} <= 19P^{3/4} once P >= 4096", 0.6 * 0.35**-0.5 <= 1.1 and 8 * 4096**0.5 <= 4096**0.75),
        ("L5.2(i) Stage 6: (D2)(a) smooth ratio 21/0.35 = 60; (D2)(a) boundary 2*0.35^{-1/2} = 3.38 <= 3.4; (D2)(b) 0.4/0.35 = 1.143 <= 1.2; (D3) 12/0.35 = 34.3 <= 35 and 6/0.35 <= 18; 9/0.35 = 25.7 <= 26", F(21) / F(35, 100) <= 60 and 2 * 0.35**-0.5 <= 3.4 and F(4, 10) / F(35, 100) <= F(12, 10) and F(12) / F(35, 100) <= 35 and F(6) / F(35, 100) <= 18 and F(9) / F(35, 100) <= 26),
        ("L5.2(i) Stage 6 (D2)(a): substituting T = P^{1/2} would give only 1/2-5/4 = -3/4, ratio O(1/(uh)) -- not o(1)", F(1, 2) - F(5, 4) == -F(3, 4) and -F(3, 4) + F(3, 4) == 0),
        # --- second reading of Theorem 5.3, Step 5a (4 Sep 2026) ---
        ("T5.3 Step 5a: lambda_a = (729/512)k|j|n^{-1/8} in [(729/512)2^{-1/8}, 729/512] = [1.3057, 1.4238], printed [1.30, 1.43] (was [1.2, 1.5])", (729 / 512) * 2**-0.125 >= 1.30 and 729 / 512 <= 1.43),
        ("T5.3 Step 5a: B' = (27/128)k|j|nu^{-5/8}; 27/128 = 0.2109 EXCEEDS the printed 0.2 -- corrected to 0.22", F(27, 128) > F(2, 10) and F(27, 128) <= F(22, 100)),
        ("T5.3 Step 5a: windows = total drift (9/16)(2^{3/8}-1)k|j|P^{3/8} = 0.16697 <= 0.17 printed (was 1.2)", (9 / 16) * (2**0.375 - 1) <= 0.17),
        ("T5.3 Step 5a: min window length 1/B'(P) = 128/27 = 4.741 >= 4.7 printed (was 0.8)", F(128, 27) >= F(47, 10)),
        ("T5.3 Step 5a: lambda_a^{-1/2} <= 1.3057^{-1/2} = 0.8752 <= 0.88 printed (was 0.92); boundary 0.17*0.88 = 0.150 <= 0.15", ((729 / 512) * 2**-0.125) ** -0.5 <= 0.88 and 0.17 * 0.88 <= 0.1500001),
        ("T5.3 Step 5a: collision M = max(lambda_a, |wX''|) with |wX''| in [1/4,4]lambda_a -> [1.3057, 4*1.4238] = [1.30, 5.70] <= printed [1.30, 5.75] (was [0.3, 6])", (729 / 512) * 2**-0.125 >= 1.30 and 4 * (729 / 512) <= 5.75),
        ("T5.3 Step 5a: collision sums P*M^{1/2} = 5.75^{1/2} = 2.398 <= 2.4; 0.17*1.30^{-1/2} = 0.149 <= 0.15; 0.17*(1/1.30)^{1/3} = 0.156 <= 0.16; times 3^{2/3} = 0.324 <= 0.33", 5.75**0.5 <= 2.4 and 0.17 * 1.30**-0.5 <= 0.15 and 0.17 * (1 / 1.30) ** (1 / 3) <= 0.16 and 0.17 * (1 / 1.30) ** (1 / 3) * 3 ** (2 / 3) <= 0.33),
        ("T5.3 Step 5a: run sums P*lambda_a^{1/2} = 1.4238^{1/2} = 1.193 <= 1.2 (was 1.3); 22*0.8752 = 19.25 <= 20 (was 21)", (729 / 512) ** 0.5 <= 1.2 and 22 * ((729 / 512) * 2**-0.125) ** -0.5 <= 20),
        ("T5.3 Step 5a exponents: 3/8+1/16 = 7/16 ; 1-1/16 = 15/16 ; 3/8+3/8 = 3/4 ; (2/3)(1/24) = 1/36 ; 15/16+1/48 = 23/24", F(3, 8) + F(1, 16) == F(7, 16) and 1 - F(1, 16) == F(15, 16) and F(3, 8) + F(3, 8) == F(3, 4) and F(2, 3) * F(1, 24) == F(1, 36) and F(15, 16) + F(1, 48) == F(23, 24)),
        # --- adversarial audit of Lemma 5.2b / Theorem 5.3 Step 5b (4 Sep 2026) ---
        # Target 1: interpolation identity -- origin and exponent of each term of f''-Lambda.
        ("L5.2b (i): gap identity gives |G_i - delta_i| = |kappa - {delta}| <= 1, NOT < 2; the printed bound (9/32)(u+u')P^{-5/4} needs <=1 (with <2 it would be (9/16))", F(9, 32) * 2 == F(9, 16)),
        ("L5.2b (ii): |b1b2 - bt1bt2| <= 4.3(h1+h2)P^{1/2}+2, times 135/1024 gives 0.567 k(h1+h2)P^{-9/8} <= 8 printed", (135 / 1024) * 4.3 <= 8),
        ("L5.2b (iii): |c''| = (27/256)k nu^{-7/8} = 0.1055 <= 0.11 printed; and 0.11 kP^{-7/8} <= 0.11P^{-5/6} iff k <= P^{1/24} (C3)", F(27, 256) <= F(11, 100) and F(7, 8) - F(5, 6) == F(1, 24)),
        ("L5.2b total: (9/32)(720) = 202.5 and 8k(h1+h2)P^{-9/8} <= 16 P^{-25/24}; 202.5+16 = 218.5 <= 219 printed", F(9, 32) * 720 + 16 <= 219 and F(1, 24) + F(1, 24) - F(9, 8) == -F(25, 24)),
        # Target 2: uniformity -- the bound is band-conditional, now hypothesis (C5).
        ("L5.2b: the 219 bound needs u,u' <= 360P^{5/24} (now hypothesis (C5)); (C1)-(C4) alone allow u <= P^{1/2}, giving (9/16)P^{-3/4} -- larger by P^{7/24}", F(1, 2) - F(5, 24) == F(7, 24)),
        ("L5.2b (C5) is met in the band: Step 5b derives u <= 200 k h2 P^{1/8} <= 200 P^{5/24} from k h2 <= P^{1/12}, and (C3)+(C4) give exactly that", F(5, 24) - F(1, 8) == F(1, 12) and F(1, 24) + F(1, 24) == F(1, 12)),
        # Target 3: three-term sublevel step.
        ("Step 5b: a = -(27/32)(16/5) = -27/10 and b = -(243/128)(64/33) = -81/22 match the printed Phi coefficients", F(-27, 32) * F(16, 5) == F(-27, 10) and F(-243, 128) * F(64, 33) == F(-81, 22)),
        ("Step 5b: lambda_0 = (27/128)k b1b2 nu^{-13/8} in [0.615, 3.900] k h1h2 P^{-5/8}, inside printed [0.56, 4.2]", (27 / 128) * 9 * 2**-1.625 >= 0.56 and (27 / 128) * 4.3**2 <= 4.2),
        ("Step 5b: V/S = 3(0.35)^{-1/2}P^{5/16-11/24} = 5.07 P^{-7/48} <= 5.1 printed", F(5, 16) - F(11, 24) == -F(7, 48) and 3 * 0.35**-0.5 <= 5.1),
        ("Step 5b: V <= c_7 S/2 needs P >= 5.8e23 at c_7=1/288 (just inside P_0 ~ 1e24) and P >= 1.3e23 at the exact c_7=1/232", (2 * 288 * 5.07) ** (48 / 7) < 1e24 and (2 * 232 * 5.07) ** (48 / 7) < 2e23),
        ("Step 5b: V >= 3(0.35)^{1/2}P^{-37/48} = 1.775 >= 1.7 printed; V >= 10|f''-Lambda| from P ~ 4e12", F(-5, 16) - F(11, 24) == -F(37, 48) and 3 * 0.35**0.5 >= 1.7),
        # Target 4: final partition.
        ("Step 5b: |Omega| <= P(V/S)^{1/2} = 5.07^{1/2} P^{89/96} = 2.252 <= 2.3 printed; 1-7/96 = 89/96", 5.07**0.5 <= 2.3 and 1 - F(7, 96) == F(89, 96)),
        ("Step 5b: boundaries (0.9*1.7)^{-1/2} = 0.809 <= 0.91 printed; 3.5*0.91 = 3.185 <= 3.2; 13/24+37/96 = 89/96", (0.9 * 1.7) ** -0.5 <= 0.91 and 3.5 * 0.91 <= 3.2 and F(13, 24) + F(37, 96) == F(89, 96)),
        ("Step 5b: S upper -- |uh1+u'h2| <= 2max = 2mu/0.84 and mu <= 60(2.6)kh1h2P^{-5/8} gives 372, NOT the printed 300; corrected to 380, good-pieces 18 -> 21", 2 * 60 * 2.6 / 0.84 > 300 and 2 * 60 * 2.6 / 0.84 <= 380 and (1.1 * 380) ** 0.5 <= 21),
        ("Step 5b: C(E)P^{89/96}log P <= P^{15/16} needs ln P >= 96 ln ln P, i.e. P ~ 1e274; at P_0 = 1e24, ln P = 55.3 > P^{1/96} = 1.78 -- the sharp reading FAILS at P_0", F(15, 16) - F(89, 96) == F(1, 96) and 24 * 2.302585 > 10 ** (24 / 96)),
        ("Step 5b mode-dominant: 22 h1h2 P^{1/4} <= 22 P^{5/16} uses H_1 = P^{1/48}, H_2 = P^{1/24} (h1h2 <= P^{1/16}), not (C4) alone (which gives P^{1/12} -> 22P^{1/3})", F(1, 48) + F(1, 24) == F(1, 16) and F(1, 16) + F(1, 4) == F(5, 16) and F(1, 12) + F(1, 4) > F(5, 16)),
        # Lemma 3.8 / 3.9 explicit constants over E = {3/4, 5/4, 11/8, 3/2, 15/8}
        ("L3.8 c_6 minimum over E is 1/14 at (alpha,beta)=(11/8,5/4); crossing at s = 13/14", F(1, 14) == abs(1 - F(13, 14)) and F(1, 14) == abs(F(3, 4) * F(13, 14) - F(5, 8))),
        ("L3.8 rho_0(E) = c_6/8 = 1/112", F(1, 14) / 8 == F(1, 112)),
        ("L3.9 c_7(E) = 1/232 uniformly: the Step 5b triple (5/4,11/8,3/2) is the extremal one", F(1, 232) < F(1, 181) * 3),
        ("L5.2 (ii) result: sqrt(t^{-1/3} P^{23/12}) = t^{-1/6} P^{23/24}", F(23, 12) / 2 == F(23, 24)),
        ("L5.2 (D3) after differencing: 6 k h1 h2 h3 P^{-13/8} <= 6 k h1 h2 P^{1/4-13/8} = 6 k h1 h2 P^{-11/8} <= 3 k h1 h2 P^{-5/8}", F(1, 4) - F(13, 8) == -F(11, 8) and -F(11, 8) < -F(5, 8)),
        # Lemma 5.2 (i) stages
        ("L5.2 Stage 1: u Delta E <= u P^{-3/4}; total u P^{1/4} <= P^{1/2+1/4} = P^{3/4} (uh <= P^{1/2})", F(1, 2) + F(1, 4) == F(3, 4)),
        ("L5.2 Stage 2: majorant 4P/R0 = 4P^{3/4} at R0 = P^{1/4}", 1 - F(1, 4) == F(3, 4)),
        ("L5.2 Stage 3 (s1): uh <= P^{3/16} gives |B| <= 2.25 P^{3/16-1/4} = 2.25 P^{-1/16}", F(3, 16) - F(1, 4) == -F(1, 16)),
        ("L5.2 Stage 3 (s2): windows 0.6 P^{1/4}; boundary cost P^{1/4-3/32+3/8} = P^{17/32} <= P^{5/8}", F(1, 4) - F(3, 32) + F(3, 8) == F(17, 32) and F(17, 32) < F(5, 8)),
        ("L5.2 Stage 4: P (uh P^{-3/4})^{1/2} = (uh)^{1/2} P^{5/8}; cells h P^{1/2} * (uh P^{-3/4})^{-1/2} = (h/u)^{1/2} P^{7/8}", 1 - F(3, 8) == F(5, 8) and F(1, 2) + F(3, 8) == F(7, 8)),
        ("L5.2 Stage 5: R0^{1/2} P^{3/4} = P^{7/8}", F(1, 8) + F(3, 4) == F(7, 8)),
        ("L5.2 Stage 5 collision (P/M)^{1/3}: P^{1/4} (P^{7/4})^{1/3} = P^{1/4+7/12} = P^{5/6}; with (uh)^{-1/3} <= P^{-1/16}: 37/48", F(1, 4) + F(7, 12) == F(5, 6) and F(5, 6) - F(1, 16) == F(37, 48)),
        ("L5.2 (D1) theta-coefficient: 24 P^{1/24-1/4} = 24 P^{-5/24}; 160 P^{1/24+1/8+1/24-3/4} = 160 P^{-13/24}", F(1, 24) - F(1, 4) == -F(5, 24) and F(1, 24) + F(1, 8) + F(1, 24) - F(3, 4) == -F(13, 24)),
        ("L5.2 (D1) curvature ratio: 80 P^{1/24-1/2}, 672 P^{1/12-1} <= P^{-1/4}", F(1, 24) - F(1, 2) < -F(1, 4) and F(1, 12) - 1 < -F(1, 4)),
        ("L5.2 (D2)(a) flat: 15 k h P^{5/8} <= 15 P^{1/24+1/8+5/8} = 15 P^{19/24} <= P^{7/8}", F(1, 24) + F(1, 8) + F(5, 8) == F(19, 24) and F(19, 24) < F(7, 8)),
        ("L5.2 (D2)(a) modes curvature (2khP^{1/8}+P^{1/2}) 3|j| P^{-5/4} <= 18 P^{-3/4} P^{-1/16}: 1/2-5/4 = -3/4 and window hypothesis room 1/16", F(1, 2) - F(5, 4) == -F(3, 4)),
        ("L5.2 (D2)(b) drift: P * h * |j| P^{-5/4} <= 13 h P^{-1/4} < 1 for h <= P^{1/8}", 1 - F(5, 4) == -F(1, 4) and F(1, 8) - F(1, 4) < 0),
        ("L5.2 (D3) ratio: k h1 h2 P^{-7/8} / u <= P^{1/8-7/8} = P^{-3/4}", F(1, 8) - F(7, 8) == -F(3, 4)),
        ("L5.2 totals: fourth term k (h/u)^{1/2} P^{1/2} <= P^{1/24} (h/u)^{1/2} P^{1/2} absorbed by (h/u)^{1/2} P^{7/8}", F(1, 24) + F(1, 2) < F(7, 8)),
        # Lemma 3.9 constant
        ("Lemma 3.9: c7 = 1/288 (inverse l^inf norm 288) -- numeric check below", True),
        # Theorem 6.1 Step E frozen-shape composites
        ("6.1 offset leftover: 945/512 - 864/512 = 81/512", F(945, 512) - F(864, 512) == F(81, 512)),
        ("6.1 kernel frozen offset 27/16 = 864/512", F(27, 16) == F(864, 512)),
        ("6.1 window-centre: 27/32 * 3/4 = 81/128 = 324/512", F(27, 32) * F(3, 4) == F(81, 128) and F(81, 128) == F(324, 512)),
        ("6.1 composite: 81/512 - 324/512 = -243/512", F(81, 512) - F(324, 512) == F(-243, 512)),
        ("6.1 B ratio to kernel: (27/32) / (9/16) = 3/2", F(27, 32) / F(9, 16) == F(3, 2)),
        ("6.1 withdrawn 405/512 = 945/512 - 540/512", F(945, 512) - F(540, 512) == F(405, 512)),
        ("6.1 smooth 4th derivative: 2*(27/8)*(19/8)*(11/8)*(3/8) = 16929/2048", F(2) * F(27, 8) * F(19, 8) * F(11, 8) * F(3, 8) == F(16929, 2048)),
        ("6.1 lambda_0' / smooth = 1095/1024 over 16929/2048 = 2190/16929", F(1095, 1024) / F(16929, 2048) == F(2190, 16929)),
        ("6.1 interpolant b': -365/176 * 11/8 * 3/8 = -1095/1024", F(-365, 176) * F(11, 8) * F(3, 8) == F(-1095, 1024)),
        ("6.1 inverse-power growth 405/243 = 5/3", F(405, 243) == F(5, 3)),
        ("6.1 offset wave ratio: -1/4 + 1/8 = -1/8", -F(1, 4) + F(1, 8) == -F(1, 8)),
        ("6.1 S upper: 1/8 - 5/8 = -1/2", F(1, 8) - F(5, 8) == -F(1, 2)),
        ("6.1 V at S = P^{-5/8}: -5/16 - 11/24 = -37/48", -F(5, 16) - F(11, 24) == -F(37, 48)),
        ("6.1 good pieces: 1 - 1/4 = 3/4", 1 - F(1, 4) == F(3, 4)),
        # --- Appendix A: the effective threshold P_0 --------------------------------------
        ("A: V = kappa S^{1/2} P^{-11/24} at S = P^{-5/8} has V/S ~ P^{-7/48}: -5/16-11/24+5/8 = -7/48",
         -F(5, 16) - F(11, 24) + F(5, 8) == -F(7, 48)),
        ("A: transition P (V/S)^{1/2} = P^{89/96}: 1 - 7/96 = 89/96", 1 - F(7, 96) == F(89, 96)),
        ("A: piece boundaries N V^{-1/2} = P^{89/96}: 13/24 + 37/96 = 89/96", F(13, 24) + F(37, 96) == F(89, 96)),
        ("A: the two P^{89/96} costs agree, so kappa^{1/2} and kappa^{-1/2} trade at fixed exponent", True),
        ("A: V <= c7 S/2 forces P^{7/48} >= 2 kappa / (c7 S_lo^{1/2}), i.e. P >= (784 kappa)^{48/7} at c7=1/232, S_lo=0.35",
         abs(2 / ((1 / 232) * 0.35 ** 0.5) - 784.2) < 1.0),
        ("A: c7 = 1/232 is 1/||M^{-1}||_inf (Lean step5b_curvature_norm), rows 110, 232, 123",
         max(10 + 68 + 32, 24 + 144 + 64, 15 + 76 + 32) == 232),
        ("A: 89/96 < 15/16 so Step 6 never needs the sharper reading", F(89, 96) < F(15, 16)),
        ("A: Weyl halving of the log power: 3 -> 3/2 -> 3/4", F(3) / 2 / 2 == F(3, 4)),
        ("A: Thm 6.3 log power 3 + 3/4 = 15/4", F(3) + F(3, 4) == F(15, 4)),
        ("A: log absorption needs ln P >= 96 A ln ln P; not used, Step 6 carries P^eps", True),
        # --- Section 6, Theorem 6.1: the depth-four identity and Step E ---
        ("6.1B: six coefficients sum to 1 at the base point (expansion exact there)",
         F(-5, 64) + F(9, 32) + F(-45, 64) + F(15, 64) + F(45, 32) + F(-9, 64) == 1),
        ("6.1B: m-derivative vanishes at the base point (v^{3/2} does not depend on m)",
         F(9, 32) + 2 * F(-45, 64) + F(45, 32) + 2 * F(-9, 64) == 0),
        ("6.1B: v-coefficient 15/64+45/32-9/64 = 3/2, so c = (3k/4) nu^{9/8}",
         F(15, 64) + F(45, 32) + F(-9, 64) == F(3, 2)),
        ("6.1B: m-block is the Taylor polynomial of -(1/2)(1+e)^{9/4}",
         [F(-1, 2) * c for c in (F(1), F(9, 4), F(9, 4) * F(5, 4) / 2)] == [F(-1, 2), F(-9, 8), F(-45, 64)]),
        ("6.1B: v-block is the Taylor polynomial of (3/2)(1+e)^{3/4}",
         [F(3, 2) * c for c in (F(1), F(3, 4), F(3, 4) * F(-1, 4) / 2)] == [F(3, 2), F(9, 8), F(-9, 64)]),
        ("6.1B: discard cost P^{-9/8} * P = P^{-1/8}, not P^{7/8}", -F(9, 8) + 1 == -F(1, 8)),
        ("6.1E: offset curvature (9/8)(15/8)(7/8) = 945/512", F(9, 8) * F(15, 8) * F(7, 8) == F(945, 512)),
        ("6.1E: kernel anchor 27/16 = 864/512", F(27, 16) == F(864, 512)),
        ("6.1E: survivor 945/512 - 864/512 = 81/512", F(945, 512) - F(864, 512) == F(81, 512)),
        ("6.1E: B = 27/32 is 3/2 times the bare kernel 9/16", F(27, 32) / F(9, 16) == F(3, 2)),
        ("6.1E: window mode (27/32)(3/4) = 324/512", F(27, 32) * F(3, 4) == F(324, 512)),
        ("6.1E: composite 81/512 - 324/512 = -243/512 != 0", F(81, 512) - F(324, 512) == F(-243, 512) != 0),
        ("6.1E: b' scales with the anchor: 405 * 1095 = 365 * 1215", 405 * 1095 == 365 * 1215),
        ("6.1E: 23/24 = 1/48 + 15/16 (k^{1/2} P^{15/16} at k <= P^{1/24})", F(1, 48) + F(15, 16) == F(23, 24)),
        # --- Section 6, Lemma 6.2 and Theorem 6.3 ---
        ("6.2: m^{9/8} at X = n^{3/2} is n^{27/16}", F(3, 2) * F(9, 8) == F(27, 16)),
        ("6.2: sawtooth exponent (3/2)(1/8) = 3/16", F(3, 2) * F(1, 8) == F(3, 16)),
        ("6.2(ii): v^{1/4} = n^{9/16}", F(9, 4) * F(1, 4) == F(9, 16)),
        ("6.3: remainder |l| P P^{-9/16} = P^{1/96+7/16} = P^{43/96}", F(1, 96) + F(7, 16) == F(43, 96)),
        ("6.3: |C| exponent 1/96 + 3/16 = 19/96", F(1, 96) + F(3, 16) == F(19, 96)),
        ("6.3: window margin 19/96 - 1/4 = -5/96 (only P^{5/96}, hence the high threshold)",
         F(19, 96) - F(1, 4) == F(-5, 96)),
        ("6.3: (i/2)X passenger 1/4 + 1/16 - 5/2 = -35/16", F(1, 4) + F(1, 16) - F(5, 2) == F(-35, 16)),
        ("6.3: -35/16 is inside the (D3) budget P^{-13/8}, ratio P^{-9/16}",
         F(-35, 16) - F(-13, 8) == F(-9, 16)),
        ("6.3 OOEO*: C_net = 27/32 - 9/16 = 9/32", F(27, 32) - F(9, 16) == F(9, 32)),
        ("6.3 OOEO*: window curvature (9/32)(3/4) = 216/1024", F(9, 32) * F(3, 4) == F(216, 1024)),
        ("6.3 OOEO*: leading coefficient 1/2 - 3/4 = -1/4", F(1, 2) - F(3, 4) == F(-1, 4)),
        ("6.3 OOEO*: curvature -(1/4)(27/16)(11/16) = -297/1024", F(-1, 4) * F(27, 16) * F(11, 16) == F(-297, 1024)),
        ("6.3 OOEO*: composite -297/1024 + 216/1024 = -81/1024 != 0",
         F(-297, 1024) + F(216, 1024) == F(-81, 1024) != 0),
        ("6.3 OOEO*: L_B lambda^{1/2} = P^{7/16-5/32} = P^{9/32}", F(7, 16) - F(5, 32) == F(9, 32)),
        ("6.3 OOEO*: k P^{9/16} intervals give P^{9/16+9/32} = P^{27/32}", F(9, 16) + F(9, 32) == F(27, 32)),
        # superseded with the Theorem 6.3 erratum: that balance belongs to the proof that
        # dropped the jY/2 mode of the four-wave product
        ("6.3 OOEO*: superseded balance at J = P^{5/48} gave P^{43/48}",
         F(1, 2) * F(5, 48) + F(27, 32) == F(43, 48) and 1 - F(5, 48) == F(43, 48)),
        ("6.3 OOEO*: surviving balance, truncation P^{-a} against mixed P^{-1/32+a/2}"
         " meets at a = 1/48, giving P^{47/48}",
         -F(1, 32) + F(1, 48) / 2 == -F(1, 48) and 1 - F(1, 48) == F(47, 48)),
        ("6.4: densities 1/2+1/4+1/16+1/32+1/32 = 7/8",
         F(1, 2) + F(1, 4) + F(1, 16) + F(1, 32) + F(1, 32) == F(7, 8)),
        ("6.4: error is the worse exponent, 47/48 <= 1 - 1/96", F(47, 48) <= 1 - F(1, 96)),
        ("6.4: the margin is one ninety-sixth, where 43/48 had nine",
         1 - F(1, 96) - F(47, 48) == F(1, 96) and 1 - F(1, 96) - F(43, 48) == F(9, 96)),
        # --- Stage 2's truncation R_0 = P^(5/16): the four sites it decides ---
        ("R_0: Stage 2 majorant 4P/R_0 = 4P^{11/16}", 1 - F(5, 16) == F(11, 16)),
        ("R_0: collision band R_0^{1/2}P^{3/4} = P^{29/32}", F(5, 32) + F(3, 4) == F(29, 32)),
        ("R_0: 29/32 inside 23/24 with 5/96 to spare", F(23, 24) - F(29, 32) == F(5, 96)),
        ("R_0: 5/16 > 7/24, so R_0 dominates 1.85 k h P^{1/8} in |q''|", F(5, 16) > F(7, 24)),
        ("R_0: |q''| curvature 5/16 - 5/4 = -15/16", F(5, 16) - F(5, 4) == F(-15, 16)),
        ("R_0: |q''| ratio -15/16 + 3/4 = -3/16, still o(1)", F(-15, 16) + F(3, 4) == F(-3, 16)),
        ("R_0: window margin 5/16 - 19/96 = 11/96 (was 5/96 at R_0 = P^{1/4})",
         F(5, 16) - F(19, 96) == F(11, 96) and F(1, 4) - F(19, 96) == F(5, 96)),
        ("R_0: flat cost per block 1 - 11/96 inside 1 - 1/96", 1 - F(11, 96) <= 1 - F(1, 96)),
        # At R_0 = P^{1/4} the flat-cost exponent clears, but only by 4/96, and the constant
        # 8*(9/8)*2^(3/16) = 10.25 then costs 10.25^24 = 1.8e24 before it is absorbed.  At
        # R_0 = P^{5/16} the gap is 10/96 and the same constant costs only 10.25^(9.6) = 5.0e9.
        ("R_0: flat-cost exponent gap is 4/96 at P^{1/4} and 10/96 at P^{5/16}",
         (1 - F(1, 96)) - (1 - F(5, 96)) == F(4, 96)
         and (1 - F(1, 96)) - (1 - F(11, 96)) == F(10, 96)),
        ("R_0: constant 10.25 absorbed at 10.25^24 = 1.8e24 vs 10.25^9.6 = 5.0e9",
         10.25 ** (96 / 4) > 1.7e24 and 10.25 ** (96 / 10) < 5.2e9),
        ("R_0: upper limit a <= 5/12 from the collision band", F(5, 16) <= F(5, 12)),
        ("R_0: lower limit a > 19/96 from the window", F(5, 16) > F(19, 96)),
        ("6.3: (i/2)X passenger at |i| <= 2P^{5/16}: 5/16 + 1/16 - 5/2 = -17/8",
         F(5, 16) + F(1, 16) - F(5, 2) == F(-17, 8)),
        ("6.3: -17/8 inside (D3) P^{-13/8} by P^{-1/2}", F(-17, 8) + F(13, 8) == F(-1, 2)),
        # Section 7, the frontier: no layer of the audit had reached these
        ("7.2: z ~ n^{27/8} so the weight rho = (3/4)k z^{1/2} ~ n^{27/16}", F(27, 8) * F(1, 2) == F(27, 16)),
        ("7.2: rho' ~ n^{11/16}: 27/16 - 1 = 11/16", F(27, 16) - 1 == F(11, 16)),
        ("7.3: level-3 smooth model n^{27/8} has G''' ~ P^{3/8} and G'''' ~ P^{-5/8}", F(27, 8) - 3 == F(3, 8) and F(27, 8) - 4 == -F(5, 8)),
        ("7.3: level-2 model n^{9/4} has Y'' ~ P^{1/4} and Y''' ~ P^{-3/4}, whence two differencings against three", F(9, 4) - 2 == F(1, 4) and F(9, 4) - 3 == -F(3, 4)),
        ("7.3: v ~ n^{9/4} jumps by n^{5/4} per step", F(9, 4) - 1 == F(5, 4)),
        ("7.3: the inner linearization trades theta_3 for a family at rho * m^{3/4} = 27/16 + 9/8 = 45/16", F(27, 16) + F(3, 2) * F(3, 4) == F(45, 16)),
        ("7.3: 45/16 > 9/4, the threshold where the paper's methods stop", F(45, 16) > F(9, 4)),
        ("7.4 model dichotomy: A ~ n^c gives A' ~ n^{c-1}, so A' >> 1 iff c > 1; the instance c = 27/16", F(27, 16) - 1 > 0),
        ("7.4 the table sorts by the same test: 3/16 and 9/16 windowed, 33/32 and 45/32 not", F(3, 16) < 1 and F(9, 16) < 1 and F(33, 32) > 1 and F(45, 32) > 1),
        ("7.3 density of the two length-five contractors plus OOOO*: 1/32+1/32+1/16 = 1/8", F(1, 32) + F(1, 32) + F(1, 16) == F(1, 8)),
        # the caps themselves: a parameter capped at C P^e is pinned to 1 until P = (2/C)^(1/e)
        ("caps: k, h_2, |l| at P^{1/24} admit a second value only from 2^24 = 16777216", 2**24 == 16777216),
        ("caps: h_1 at P^{1/48} needs 2^48, which is above P_0 = 3.6e13 while 2^24 is below it", 2**48 > 3.6e13 > 2**24),
        ("caps: h with h^{1/2} <= P^{1/24}, i.e. h <= P^{1/12}, needs only 2^12 = 4096", 2**12 == 4096),
        ("caps: j <= 2P^{1/24} is never pinned, (2/2)^{24} = 1", (F(2, 2)) ** 24 == 1),
        # the two Lemma 5.1(iii) bracket constants, which the census measures to seven digits
        ("5.1(iii) first bracket: (3/2) m^{1/2} j with m ~ n^{3/2} gives (3/2) j n^{3/4}", F(3, 2) * F(3, 4) == F(9, 8) and F(3, 4) == 1 - F(1, 4)),
        ("5.1(iii) second bracket: (3/4) m^{-1/2} b1 b2 with b_i ~ 3 h_i n^{1/2} gives (27/4) h1 h2 n^{1/4}", F(3, 4) * 3 * 3 == F(27, 4)),
        ("5.1(iii) over a dyadic block the true bands are [3/2, (3/2)2^{3/4}] and [27/4, (27/4)2^{1/4}]", F(3, 2) < F(26, 10) and F(27, 4) < 15),
        # Theorem 6.1 Step B, where the mode cap |k| <= 2P^{1/96} makes the discard cost exact
        ("6.1 Step B: 1/96 - 1/8 = -11/96, so (3pi k/4)P^{-1/8} <= (3pi/2) P^{-11/96}", F(1, 96) - F(1, 8) == -F(11, 96)),
        ("6.1 Step B: the printed 4.8 is above the exact 3pi/2 = 4.7124, so 7.6e5 is that constant's threshold, not 4.8's", 4.8 > 3 * math.pi / 2 and (3 * math.pi / 2) ** (96 / 11) < 7.6e5 < 4.8 ** (96 / 11)),
        # Step 5b's pairing: the interpolant error and S are bounded at settings no cell realizes
        ("5b pairing: E_first/S carries (h1+h2)/(h1 h2) = 1/h1 + 1/h2 <= 2, independent of k", F(1) + F(1) == 2),
        ("5b pairing: -25/24 + 5/8 = -5/12 charged where -9/8 + 5/8 = -1/2 is available, a gap of 1/12", -F(25, 24) + F(5, 8) == -F(5, 12) and -F(9, 8) + F(5, 8) == -F(1, 2) and -F(5, 12) + F(1, 2) == F(1, 12)),
        ("5b pairing: k h1 h2 = 1 over the integers forces k = h1 = h2 = 1, hence k(h1+h2) = 2", 1 * 1 * 1 == 1 and 1 * (1 + 1) == 2),
        # st5b-qpp: the same mismatch in h, and the c-rows that get it right
        ("st5b-qpp: h cancels in 1.85 k h P^{1/8}/(u h), leaving 1.85 k P^{1/8}/u with 1/24+1/8 = 1/6", F(1, 24) + F(1, 8) == F(1, 6)),
        ("st5b-qpp: the charged 7/24 exceeds that 1/6 by exactly 1/8", F(7, 24) - F(1, 6) == F(1, 8)),
        ("39-c rows pair correctly: |c''/2| ~ k P^{-7/8} over S ~ k h1 h2 P^{-5/8} cancels k, leaving -1/4", -F(7, 8) + F(5, 8) == -F(1, 4)),
        # Appendix A.5: the three middle-band costs and the amplification of every constant in P_1
        ("A.5: V ~ P^{-37/48} from S ~ P^{-5/8}, so the boundary term is P^{13/24+37/96} = P^{89/96}", F(13, 24) + F(37, 96) == F(89, 96)),
        ("A.5: the r=3 term at 41/48 = 82/96 sits below the two that share 89/96", F(41, 48) == F(82, 96) and F(82, 96) < F(89, 96)),
        ("A.5: P_1 solves C P^{89/96} = P, so P_1 = C^{96/7} and a constant is amplified by 96/7", 1 - F(89, 96) == F(7, 96)),
        ("A.5: the piece count is 3 + 2P^{-13/24} + 22P^{-11/48} + 5P^{-5/24}, leading 3 from 1/24+1/2", F(1, 24) + F(1, 2) == F(13, 24) and F(5, 16) - F(13, 24) == -F(11, 48) and F(1, 3) - F(13, 24) == -F(5, 24)),
        # Lemma 3.9's proof of the r=4 length, whose constant A.5 does not carry
        ("3.9 proof: 4V >= (c_7 S/(4P^2))(y-x)^2/4 gives (y-x)^2 <= 64 V P^2/(c_7 S), i.e. 8P", 64 ** 0.5 == 8.0),
        ("3.9 proof: the r=3 length 4PV/(c_7 S) and the r=4 length 8P(V/(c_7 S))^{1/2} differ in shape, so one C(E) scales them differently", F(1) != F(1, 2)),
        # Corollary 4.9's density and its depth-five extension, which nothing had checked
        ("4.9: 1/2 + 1/4 + 1/16 = 13/16, the certified-descent density through depth four", F(1, 2) + F(1, 4) + F(1, 16) == F(13, 16)),
        ("4.9 with 6.3's two contractors: 13/16 + 1/32 + 1/32 = 7/8", F(13, 16) + F(1, 32) + F(1, 32) == F(7, 8)),
        # Lemma 4.6's two-term expansion, and why its lower end is exactly theta
        ("4.6: m^{3/4} = n^{9/8} - (3/4) theta n^{-3/8} + ..., from 9/8 - 3/2 = -3/8", F(9, 8) - F(3, 2) == -F(3, 8)),
        ("4.6: the theta_2 term sits at -9/8 and the residual at -15/8 = -3/8 - 3/2", -F(3, 8) - F(3, 2) == -F(15, 8)),
        ("4.6: so D/lower = theta + O(n^{-3/4}), the two ends differing by -9/8 + 3/8 = -3/4", -F(9, 8) + F(3, 8) == -F(3, 4)),
        # Corollary 4.13(a)'s nesting, whose sharp constant is 3/8 where 1 is printed
        ("4.13(a): n^{9/16} - v^{1/4} = (3/8) theta n^{-15/16} + (1/4) theta_2 n^{-27/16}, from 9/16 - 3/2 = -15/16", F(9, 16) - F(3, 2) == -F(15, 16)),
        ("4.13(a): the second term sits at -27/16 = -15/16 - 3/4, so the ratio is (3/8) theta + O(n^{-3/4})", -F(15, 16) - F(3, 4) == -F(27, 16)),
        ("4.13: the printed error m'^{-4/27} reaches 10% only at m' = 10^{27/4}", F(4, 27) * F(27, 4) == 1),
        # Lemma 4.10's application: the twist's total variation in the regime it is used in
        ("4.10: TV <= 2h|I| sup|g''| <= 0.26 P^{1/24+1/12+1-23/16} = 0.26 P^{-5/16}", F(1, 24) + F(1, 12) + 1 - F(23, 16) == -F(5, 16)),
        # Lemma 3.3's A-process display: where its 2 and 4 come from, and what they cost
        ("3.3 A-process: (1/2) from the classical inequality times (1/4) from the simplification is 1/8", F(1, 2) * F(1, 4) == F(1, 8)),
        # the transcription rule: which end of the dyadic block a pointwise check must assume
        ("5.1(iii): the slip costs 2^{3/4} on the first bracket and 2^{1/4} on the second, the band's own exponents", F(3, 4) - F(1, 4) == F(1, 2)),
        ("5.1(iv): M_1's exponent is negative, so P = n is the smallest right-hand side and already strict", -F(7, 8) < 0),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]


def appendix_a6_checks() -> list[dict[str, Any]]:
    """Appendix A.6's lever arithmetic: the `c_7` ceiling and the `R_0` minimax.

    These constants entered the manuscript after the exponent tables were written and had no
    audit coverage, which is how the Paper A exponent drifted.  Each is a relation between
    numbers the appendix prints, recomputed here from those numbers alone.
    """

    def approx(a: float, b: float, rel: float = 0.02) -> bool:
        return abs(a - b) <= rel * abs(b)

    # the c_7 lever: what it buys in total, and where it stops
    gain = 3.5858e13 / 2.98e11
    # the R_0-dependent sites, at the three exponents the appendix quotes
    sites = {"P^{5/16}": 2.98e11, "P^{9/32}": 7.4e13, "P^{1/3}": 1.6e12}
    # Section 5's (i) sum and the bound it doubles to
    sum_i_exact, sum_i_printed = 85.2820, 85.3

    checks: list[tuple[str, bool]] = [
        ("A.6 c_7 lever buys 3.6e13 -> 2.98e11, printed as a factor 120",
         approx(gain, 120.3, 0.01)),
        ("A.6 next threshold 2.83e10 is an order below the 2.98e11 floor",
         5.0 <= 2.98e11 / 2.83e10 <= 20.0),
        ("A.6 the floor is the minimax over R_0, attained at P^{5/16}",
         min(sites, key=lambda k: sites[k]) == "P^{5/16}"),
        ("A.6 'a threshold below 3e11 needs a different site': the floor is below 3e11",
         2.98e11 < 3.0e11),
        ("(i) 85.2820 <= 85.3 and the doubled bound 170.6 is printed 171",
         sum_i_exact <= sum_i_printed and approx(2 * sum_i_printed, 170.6, 1e-9) and 170.6 <= 171.0),
        ("the third displayed term 0.9070 is printed 0.91, and 0.95 would pass 85.3",
         round(0.9070, 2) == 0.91 and sum_i_exact - 0.9070 + 0.95 > 85.3),
        ("the earlier draft's 8 is nine times the true 0.9070",
         approx(8.0 / 0.9070, 8.82, 0.02)),
        # the earlier draft's printed 219 is 202.5 + 16 = 218.5 rounded up, the same
        # convention as 105.8 -> 106; recorded so the 0.5 is not read as an error
        ("earlier draft: 202.5 + 16 = 218.5, printed 219 by the same round-up as 170.6 -> 171",
         approx(202.5 + 16.0, 218.5, 1e-9) and 218.5 <= 219.0),
    ]
    return [{"check": name, "ok": ok} for name, ok in checks]
