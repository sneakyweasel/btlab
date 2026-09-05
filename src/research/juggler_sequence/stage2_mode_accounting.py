"""Stage-2 / Stage-5 mode accounting in Lemma 5.2(i), and what widening q' does to it.

Run as a script.  Every number printed is exact rational arithmetic on the exponents;
nothing here is a numerical experiment.

Two separate questions, which I had conflated in the draft:

  (a) INDEX RANGE.  Lemma 3.7 produces modes of index <= |B| + J.  In the printed case
      |B| <= 1 and J = R_0, so |w| <~ R_0.  Under (D1'), |B| <= 7 P^(1/4).  Is that still
      within a constant multiple of R_0 = P^(5/16), the way (D2)'s 2.85 R_0 is?

  (b) WEIGHTS.  Stage 3 splits on the size of the sawtooth coefficient B: regime (s1),
      uh <= P^(3/16), has |B| <= 2.25 P^(-1/16) and hands the modes a damping factor
      min(2, 2 pi |B|) <= 14.2 P^(-1/16).  Regime (s2) has large B and instead windows.
      A widened q' has large B, so its decoration leaves (s1) for (s2).
"""

from fractions import Fraction as F

P0 = 8.9458e13

print("(a) index range under (D1'):")
print("    R_0 = P^5/16 = P^%s" % F(5, 16))
print("    |B| <= 7 P^1/4; 7 P^(1/4) <= P^(5/16) iff P >= 7^16 = %.4g" % (7.0 ** 16))
print("    P_0 = %.4g, so the comparison holds at P_0: %s" % (P0, 7.0 ** 16 <= P0))
print("    hence |w| <= |B| + R_0 <= 2 R_0 -- the same shape as (D2)'s 2.85 R_0")
print()

print("(b) Stage 5's dominant-mode sum over the Stage-2 families:")
print("    per mode  1.4 |w|^(1/2) P^(3/4), weight 1/|w|, summed over |w| <= R_0")
print("    -> 2.8 R_0^(1/2) P^(3/4) = 2.8 P^(%s) = 2.8 P^(%s)"
      % (F(5, 32) + F(3, 4), float(F(5, 32) + F(3, 4))))
printed = F(7, 8)
stage5 = F(5, 32) + F(3, 4)
print("    printed in the manuscript: 3 P^(29/32); 29/32 = %s  [match: %s]"
      % (float(F(29, 32)), stage5 == F(29, 32)))
print("    largest exponent in Lemma 5.2(i)'s conclusion: 7/8 = %s" % float(printed))
print("    29/32 - 7/8 = %s  -> the mode sum EXCEEDS the printed bound by P^(1/32)"
      % (stage5 - printed))
print()

print("    unless a printed term reaches P^(29/32).  The four terms, at u = h:")
for e in (F(1, 32), F(2, 32), F(3, 32), F(4, 32)):
    uh = 2 * e
    terms = {
        "(uh)^1/2 P^5/8": uh / 2 + F(5, 8),
        "(h/u)^1/2 P^7/8": F(0) + F(7, 8),          # h = u, so (h/u)^(1/2) = 1
        "P^7/8": F(7, 8),
        "P^1/24 (uh)^-1/2 P^7/8": F(1, 24) - uh / 2 + F(7, 8),
    }
    best = max(terms.values())
    print("      u = h = P^%-5s (uh = P^%-5s): max printed = P^%-8s vs mode sum P^%s  %s"
          % (e, uh, float(best), float(stage5),
             "OK" if best >= stage5 else "PRINTED BOUND IS SMALLER"))
print()
print("    (s1) requires uh <= P^3/16 = P^%s" % float(F(3, 16)))
print("    with the (s1) damping factor 14.2 P^(-1/16): 29/32 - 2/32 = %s < 7/8 = %s"
      % (float(F(27, 32)), float(F(7, 8))))
