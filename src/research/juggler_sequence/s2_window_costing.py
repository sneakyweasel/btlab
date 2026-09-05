"""The (s2) window costing for a widened decoration's sawtooth.

Stage 3(s2) is the template: a sawtooth whose coefficient B is too large for |B| <= 1 is
windowed so that B moves by at most 1 per window, Lemma 3.7 is applied at each window centre,
and three costs are paid -- the window count times a boundary charge, the Lemma 3.7 flat cost,
and the modes, which go to Stage 5.

Under (D1') the decoration's sawtooth has |B| <= 7 P^(1/4) in place of <= 1, so it needs the
same treatment.  Every line below is the (s2) line with 2.25 replaced by 7.
"""

from fractions import Fraction as F

# --- Stage 3(s2), the printed template ---------------------------------------
B_MAIN = 2.25          # |B| <= 2.25 P^(1/4)
WIN_MAIN = 0.6         # at most 0.6 P^(1/4) + 1 windows
FLAT_MAIN = 19.0       # flat cost <= 19 P^(3/4) in total

# --- the widened decoration ---------------------------------------------------
# |B| <= |q'|(2|j'| P^(-1/4) + 20 h h' P^(-3/4)) and |q'| h' <= P^(1/2), |j'| <= 3, h <= P^(1/8)
#      <= 6 P^(1/4)/h' + 20 h P^(-1/4)  <=  6 P^(1/4) + 20 P^(-1/8)
B_DEC = 7.0            # opened from 6 + o(1)

MAIN_CURV = 0.35       # Stage-4 curvature 0.35 u h P^(-3/4)


def lemma37_threshold(bcoef: float) -> float:
    """Least P^(1/4) with P^(1/2) >= 8(1 + b P^(1/4)), i.e. x^2 - 8 b x - 8 >= 0."""
    b = 8.0 * bcoef
    return (b + (b * b + 32.0) ** 0.5) / 2.0


print("Lemma 3.7 hypothesis T = P^(1/2) >= 8(1+|B|):")
for name, b in (("main sawtooth", B_MAIN), ("widened decoration", B_DEC)):
    x = lemma37_threshold(b)
    print("   %-20s needs P^(1/4) >= %6.2f, i.e. P >= %.3g" % (name, x, x ** 4))
print("   P_0 = 8.9458e13 clears both: %s" % (lemma37_threshold(B_DEC) ** 4 < 8.9458e13))
print()

print("window count (B monotone on the dyadic block, so total drift <= sup|B|):")
print("   main sawtooth      %.2f P^(1/4) + 1   [printed]" % WIN_MAIN)
print("   widened decoration %.2f P^(1/4) + 1   [conservative: full range]" % B_DEC)
print("   refinement: B is a degree -1/4 monomial in n, so the drift over (P,2P] is")
print("               (1 - 2^(-1/4)) |B(P)| = %.3f |B(P)| <= %.2f P^(1/4)"
      % (1 - 2 ** -0.25, (1 - 2 ** -0.25) * B_DEC))
print()

boundary_const = (B_DEC + 1) * MAIN_CURV ** -0.5
print("boundary cost = (windows) x (0.35 u h)^(-1/2) P^(3/8):")
print("   main sawtooth      <= (0.6 P^(1/4)+1)(0.35uh)^(-1/2) P^(3/8) <= 1.1 P^(17/32)"
      " [uses uh > P^(3/16), available in (s2)]")
print("   widened decoration <= %.1f (uh)^(-1/2) P^(5/8)   [no lower bound on uh needed]"
      % boundary_const)
print("      exponent 5/8 = %s; (i)'s fourth term carries (uh)^(-1/2) P^(1/24+7/8) = P^%s"
      % (F(5, 8), F(1, 24) + F(7, 8)))
print("      so it is dominated for every uh >= 1: %s" % (F(5, 8) < F(1, 24) + F(7, 8)))
print()

flat_dec = 8.0 * B_DEC + 8.0
print("Lemma 3.7 flat cost 8(1+|B|) P^(1/2), summed:")
print("   main sawtooth      <= %.0f P^(3/4)  [printed]" % FLAT_MAIN)
print("   widened decoration <= %.0f P^(3/4)" % flat_dec)
print("      3/4 = %s, inside (i)'s 7/8: %s" % (F(3, 4), F(3, 4) < F(7, 8)))
print()

print("modes: per window Lemma 3.7 at centre B_0 gives e(w nu^(3/2)) with weights")
print("   min(2, 1/(pi|w+B_0|)) + min(2, 1/(pi|w|)) -- the (s2) shape, not (s1)'s damping.")
print("   index range |w| <= |B_0| + R_0 <= 2 R_0 (shown last turn, valid at P >= P_0),")
print("   so Stage 5's dominant sum grows by at most 2^(1/2), and the (s2)-tail bound")
print("   C P^(7/8) log P grows by the window ratio %.0f. Both are absorbed by P^eps."
      % (B_DEC / WIN_MAIN))
print()

print("verdict: the three new costs are")
for label, expo in (("boundary", F(5, 8)), ("flat", F(3, 4)), ("modes", F(29, 32))):
    print("   %-9s P^%-6s   inside (i) amended with R_0^(1/2)P^(3/4) = P^29/32: %s"
          % (label, expo, expo <= F(29, 32)))
