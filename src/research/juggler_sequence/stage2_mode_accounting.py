"""Stage-2 / Stage-5 mode accounting in Lemma 5.2(i), and where P^(29/32) is charged.

Every number here is exact rational arithmetic on the exponents; nothing is a numerical
experiment.  The question this settles: Stage 5's dominant-mode sum over the Stage-2 families
is 3 R_0^(1/2) P^(3/4) = 3 P^(29/32), and 29/32 > 7/8, which is the largest exponent in the
conclusion of Lemma 5.2(i).  Does something bring it down?

The candidate was Stage 3's regime-(s1) damping, min(2, 2 pi |B|) <= 14.2 P^(-1/16).  It does
not apply: Stage 2 Vaaler-expands the *carry* indicator kappa at truncation R_0, giving modes
with weight 1/|r| and no B-factor, while Stage 3(s1) expands the *theta-sawtooth* "into the
same two mode families" and it is those modes that carry the damping.  Two sources, one pair of
families, one damped.

Appendix A.6 settles where the term is charged.  It states, of the move from R_0 = P^(1/4) to
P^(5/16), that "the collision-band term moves from 3P^(7/8) log P to 3P^(29/32) log P, still
inside P^(23/24) with P^(5/96) to spare".  So the term is verified against Theorem 5.3's target
P^(23/24), not against Lemma 5.2(i)'s own printed conclusion -- and at R_0 = P^(1/4), the value
an earlier draft used, it was exactly P^(7/8) and did fit.
"""

from __future__ import annotations

from fractions import Fraction as F

P0 = 8.9458e13
R0_EXPONENT = F(5, 16)
R0_EARLIER = F(1, 4)


def stage5_family_sum(a: F) -> F:
    """Exponent of Stage 5's dominant-mode sum over the Stage-2 families at R_0 = P^a.

    Per mode Lemma 3.3 gives 1.4 |r|^(1/2) P^(3/4); the Stage-2 weight is 1/|r|; summing
    r^(-1/2) over r <= R_0 gives 2 R_0^(1/2).
    """
    return a / 2 + F(3, 4)


def lemma_52i_terms(u: F, h: F) -> dict[str, F]:
    """The four printed terms of Lemma 5.2(i), as exponents of P, at u = P^u, h = P^h."""
    return {
        "(uh)^1/2 P^5/8": (u + h) / 2 + F(5, 8),
        "(h/u)^1/2 P^7/8": (h - u) / 2 + F(7, 8),
        "P^7/8": F(7, 8),
        "P^1/24 (uh)^-1/2 P^7/8": F(1, 24) - (u + h) / 2 + F(7, 8),
    }


def uncovered_corners() -> list[tuple[F, F, F, F]]:
    """(u, h, best printed term, family sum) where the printed bound falls short.

    Only regime (s1) matters: uh <= P^(3/16) makes every mode dominant, since the dominance
    threshold 9.1 u h P^(-1/4) is then below 1.
    """
    out = []
    fam = stage5_family_sum(R0_EXPONENT)
    for un in range(0, 17):
        for hn in range(0, 13):
            u, h = F(un, 96), F(hn, 96)
            if u + h > F(3, 16):          # outside regime (s1)
                continue
            if h > F(1, 8):               # outside the hypothesis of (i)
                continue
            best = max(lemma_52i_terms(u, h).values())
            if best < fam:
                out.append((u, h, best, fam))
    return out


def main() -> None:
    fam = stage5_family_sum(R0_EXPONENT)
    print("Stage-5 sum over the Stage-2 families:")
    print("   at R_0 = P^%-5s : P^%-7s (= %s)  <- the manuscript's printed 3 P^(29/32)"
          % (R0_EXPONENT, fam, float(fam)))
    print("   at R_0 = P^%-5s : P^%-7s (= %s)  <- exactly Lemma 5.2(i)'s printed 7/8"
          % (R0_EARLIER, stage5_family_sum(R0_EARLIER), float(stage5_family_sum(R0_EARLIER))))
    print()
    print("charged against Theorem 5.3's target P^(23/24), per Appendix A.6:")
    print("   23/24 - 29/32 = %s  <- A.6's \"P^(5/96) to spare\": %s"
          % (F(23, 24) - fam, F(23, 24) - fam == F(5, 96)))
    print()
    print("but against Lemma 5.2(i)'s own conclusion, in regime (s1):")
    bad = uncovered_corners()
    print("   %d admissible (u, h) where every printed term is smaller" % len(bad))
    if bad:
        worst = min(bad, key=lambda r: r[2])
        print("   worst: u = P^%-5s h = P^%-5s -> printed P^%-7s vs family sum P^%s (short by P^%s)"
              % (worst[0], worst[1], worst[2], worst[3], worst[3] - worst[2]))
        print("   e.g.  u = h = P^3/32 (the top of regime (s1)):")
        for k, v in lemma_52i_terms(F(3, 32), F(3, 32)).items():
            print("        %-26s P^%s" % (k, v))
    print()
    print("downstream consumers all target more than P^(29/32), so a fifth term is free:")
    for name, target in (("Theorem 5.3 assembly", F(23, 24)), ("Lemma 5.2(ii)", F(23, 24)),
                         ("Step 5b mode-dominant", F(15, 16))):
        print("   %-24s P^%-6s  covers P^%s: %s" % (name, target, fam, target > fam))


if __name__ == "__main__":
    main()
