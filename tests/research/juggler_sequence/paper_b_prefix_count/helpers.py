"""Independent enumerators and historical manuscript fixtures for prefix tests."""
from __future__ import annotations
import itertools
import math
from fractions import Fraction
from pathlib import Path
from research.juggler_sequence import paper_b_prefix_count as B


BETA_ = math.log(2.0) / math.log(3.0)


ROOT = Path(__file__).resolve().parents[4]


PAPER = ROOT / "docs" / "theory" / "juggler_parity_discrepancy_note_2026_09_04.md"


def surviving_words(d: int) -> list[str]:
    out: list[str] = []

    def rec(w: str, o: int, t: int) -> None:
        if t == d:
            out.append(w)
            return
        for ch, s in (("O", 1), ("E", 0)):
            if B.survives(t + 1, o + s):
                rec(w + ch, o + s, t + 1)

    rec("", 0, 0)
    return out


DEPENDENTS = {
    "docs/theory/theorem_ledger.json": "the generated claim export",
    "docs/theory/theorem_ledger.md": "rendered from the JSON",
    "docs/theory/juggler_cycle_itinerary_structure_note.md": "imports it as Proposition 6.1",
    "docs/problems/juggler_k3_rate_free.md": "derives the rate-free reduction from it",
    "docs/research/juggler_two_step_parity_lemma.md": "the source note",
}


def _all_words(lo: int, hi: int) -> list[str]:
    return ["".join(c) for d in range(lo, hi + 1)
            for c in itertools.product("OE", repeat=d)]


def _walk(w: str) -> list[float]:
    """``u_t = o_t log2(3) - t``, the exponent walk of the Paper C collision work."""
    u, o = [0.0], 0
    for i, c in enumerate(w, start=1):
        if c == "O":
            o += 1
        u.append(o * math.log2(3.0) - i)
    return u


def _beta_semiconvergent_denominators(limit: int) -> set[int]:
    """Ostrowski skeleton of BETA = log3(2): denominators q_(k-1) + j q_k."""
    x, a = BETA_, []
    for _ in range(14):
        i = math.floor(x)
        a.append(i)
        x -= i
        if x < 1e-15:
            break
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    q = q[1:]
    out = set()
    for k in range(1, len(q) - 1):
        for j in range(0, a[k + 1] + 1):
            d = q[k - 1] + j * q[k]
            if 2 <= d <= limit:
                out.add(d)
    return out


def _tilt_constants() -> tuple[float, float, float, float]:
    """(theta*, rho, p*, sigma) for the zero-drift tilt, in nats."""
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    theta = math.log(b / a) / (a + b)
    rho = 0.5 * (math.exp(theta * a) + math.exp(-theta * b))
    p = 0.5 * math.exp(theta * a) / rho
    sigma = math.sqrt(p * a * a + (1 - p) * b * b - (p * a - (1 - p) * b) ** 2)
    return theta, rho, p, sigma


def _tilted_survival_and_cost(d: int) -> tuple[float, float]:
    """P_theta(survive) and E_theta[e^{-theta S_d} | survive]."""
    theta, _rho, p, _sigma = _tilt_constants()
    a, b = math.log(3.0) - math.log(2.0), math.log(2.0)
    st = {0: 1.0}
    for step in range(1, d + 1):
        nx: dict[int, float] = {}
        for o, w in st.items():
            for do, pr in ((1, p), (0, 1 - p)):
                o2 = o + do
                if o2 * a - (step - o2) * b < -1e-15:
                    continue
                nx[o2] = nx.get(o2, 0.0) + w * pr
        st = nx
    surv = sum(st.values())
    cost = sum(w * math.exp(-theta * (o * a - (d - o) * b)) for o, w in st.items())
    return surv, cost / surv


def _endpoint_profile(d: int) -> tuple[int, list[tuple[float, float]]]:
    """(N_d, [(endpoint level, share of N_d)]) with an exact integer mask."""
    from decimal import Decimal, getcontext

    getcontext().prec = 50
    log2_3 = math.log2(3.0)
    k = 10 ** 30
    l23k = int((Decimal(3).ln() / Decimal(2).ln()) * k)
    st = {0: 1}
    for step in range(1, d + 1):
        nx: dict[int, int] = {}
        tk = step * k
        for o, c in st.items():
            for do in (0, 1):
                o2 = o + do
                if o2 * l23k >= tk:
                    nx[o2] = nx.get(o2, 0) + c
        st = nx
    tot = sum(st.values())
    return tot, sorted((o * log2_3 - d, c / tot) for o, c in st.items())


def _beta_cf_and_denominators(n: int = 30):
    from decimal import Decimal, getcontext

    getcontext().prec = 120
    beta = Decimal(2).ln() / Decimal(3).ln()
    a, x = [], beta
    for _ in range(n):
        i = int(x)
        a.append(i)
        x -= i
        if x == 0:
            break
        x = 1 / x
    q = [0, 1]
    for ai in a[1:]:
        q.append(ai * q[-1] + q[-2])
    return a, q[1:]


def _least_peak(kmax: int) -> list[float]:
    """Least achievable walk peak over non-contracting words, by length.

    State is (steps, odd letters), which fixes the level, so this is a DP rather
    than a search over 2^k words.
    """
    log2_3 = math.log2(3.0)
    f = {0: 0.0}
    out = []
    for step in range(1, kmax + 1):
        g: dict[int, float] = {}
        for a, peak in f.items():
            for da in (0, 1):
                a2 = a + da
                u = a2 * log2_3 - step
                if u < -1e-12:
                    continue
                p = max(peak, u)
                if a2 not in g or p < g[a2] - 1e-12:
                    g[a2] = p
        f = g
        out.append(min(f.values()))
    return out


def _screen_verdict(word: str, use_theorem: bool) -> bool:
    """`unobstructed`, with the E < 2 criterion optionally switched off."""
    for t_ in range(3, len(word) + 1):
        if B.deepest_blocked(word, t_) is None:
            continue
        if not B.has_branch_runs(B.branch_base(word, t_)):
            return False
        if B.beyond_methods(word, t_):
            return False
        if use_theorem and not B.linearisation_safe(word, t_):
            return False
    return True


def _iterates(n: int, d: int):
    """Actual Juggler iterates and the word n realises, at working precision."""
    from mpmath import mpf, floor, power
    it, w = [n], ""
    for _ in range(d):
        c = it[-1]
        w += "O" if c % 2 else "E"
        it.append(int(floor(power(mpf(c), mpf(3) / 2 if c % 2 else mpf(1) / 2))))
    return w, it


def _measured_coefficient(n: int, d: int, s: int):
    """d(J^d)/d(theta_s) along the real orbit: prod p_q (J^{q-1})^{p_q - 1}."""
    from mpmath import mpf, power
    w, it = _iterates(n, d)
    p = [mpf(3) / 2 if ch == "O" else mpf(1) / 2 for ch in w]
    out, v = mpf(1), mpf(it[s])
    for q in range(s + 1, d + 1):
        out *= p[q - 1] * power(v, p[q - 1] - 1)
        v = power(v, p[q - 1])
    return w, out


WITNESSES = [("OOEOOE", 1000057), ("OOOEEO", 1000091),
             ("OOOEOO", 1000069), ("OOOOOO", 1000053)]


ELEMENTARY_D4 = ["OEEE", "OEEO", "OEOE", "OEOO", "OOEE", "OOEO"]


KERNEL_D4 = ["OOOE", "OOOO"]


def _blocked_stats(root: str, d: int):
    from itertools import product
    total = blocked = sqrt_kind = 0
    for bits in product("EO", repeat=d - 1):
        w = root + "".join(bits)
        total += 1
        hits = [B.deepest_blocked(w, t) for t in range(3, d + 1) if B.deepest_blocked(w, t)]
        if hits:
            blocked += 1
            if any(h[3] == "sqrt" for h in hits):
                sqrt_kind += 1
    return total, blocked, sqrt_kind


def _proved_words() -> list[str]:
    """Everything Paper B proves: all words of depth <= 4, plus Theorem 6.3's four."""
    from itertools import product
    out = ["".join(b) for d in (2, 3, 4) for b in product("EO", repeat=d)]
    return out + ["OOOEE", "OOOEO", "OOEOE", "OOEOO"]


def _blocked_profile_of(word: str):
    out = set()
    for t in range(3, len(word) + 1):
        d = B.deepest_blocked(word, t)
        if d:
            out.add((d[0], d[3]))
    return tuple(sorted(out))


def _blocked_bruteforce(d: int) -> int:
    from itertools import product
    total = 0
    for bits in product("EO", repeat=d):
        e, o = [], 0
        for i, c in enumerate(bits, 1):
            o += c == "O"
            e.append(Fraction(3 ** o, 2 ** i))
        lo = None
        for t in range(3, d + 1):
            lo = e[t - 3] if lo is None else min(lo, e[t - 3])
            if e[t - 2] - lo > 1:
                total += 1
                break
    return total


def _theta(q: float) -> float:
    """Optimised Chernoff base for ``Pr(B_n >= q n)`` at ``p = 1/2``: ``exp(-KL(q||1/2))``."""
    return q ** (-q) * (1 - q) ** (q - 1) / 2


_BUMP_P = 2585


_BUMP_Q = 4096


def _beta_semiconvergents(limit: int) -> tuple[set[int], set[int]]:
    """Semiconvergent denominators of BETA up to ``limit``, split by the sign of the gap."""
    log2_3 = math.log2(3.0)
    x, partial = 1.0 / log2_3, []
    for _ in range(20):
        i = int(x // 1)
        partial.append(i)
        x -= i
        if x < 1e-14:
            break
        x = 1.0 / x
    q = [0, 1]
    for a in partial[1:]:
        q.append(a * q[-1] + q[-2])
    q = q[1:]

    def gap(d: int) -> float:
        o = round(d / log2_3)
        return min(((abs(c * log2_3 - d), c * log2_3 - d) for c in (o - 1, o, o + 1)))[1]

    below, above = set(), set()
    for k in range(1, len(q) - 1):
        for j in range(1, partial[k + 1] + 1):
            d = q[k - 1] + j * q[k]
            if 2 <= d <= limit:
                (below if gap(d) < 0 else above).add(d)
    return below, above
