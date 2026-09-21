"""Independent arithmetic checks for the 3n-1 m-cycle note.

Reads ``docs/theory/collatz_3n_minus_1_m_cycles_note.md`` and the probe's
``data/research/juggler/negative_m_cycles/summary.json`` and recomputes the
manuscript's numbers by a different route from the probe's:

* the admissible lengths at the floors 2^40, 2^44 and 2^48 are enumerated by an
  integer sieve over K = iQ + j with Q a convergent denominator of log2/log3
  (the probe uses the three-gap walk); the sieve is first checked against a
  direct scan at a coarse window;
* each Rhin ceiling K_3(m) is recomputed and its defining inequality evaluated
  at K_3 - 1 and K_3;
* every margin is recomputed with mpmath at one hundred digits;
* the known cycles' (K, o) are recomputed by iterating the map.

At the three larger floors only the printed survivors are checked (admissible,
below the ceiling, positive margin); their counts are the probe's. The floor
certificate, the proofs and Rhin's bound are outside this script's scope.

Writes ``data/research/juggler/negative_m_cycles/manuscript_check.json`` and
exits nonzero on any disagreement.  ``--note`` points it at another copy of
the manuscript, which is how it is shown to fail on a wrong number.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import mpmath as mp

mp.mp.dps = 120
ROOT = Path(__file__).resolve().parents[1]
NOTE = ROOT / "docs/theory/collatz_3n_minus_1_m_cycles_note.md"
SUMMARY = ROOT / "data/research/juggler/negative_m_cycles/summary.json"
OUTPUT = ROOT / "data/research/juggler/negative_m_cycles/manuscript_check.json"

LN2, LN3 = mp.log(2), mp.log(3)
X = LN2 / LN3
DELTA = 1 / X
RHIN = mp.mpf("13.3")
SCALE_BITS = 256
S = 1 << SCALE_BITS
XS = int(mp.floor(X * S))

problems: list[str] = []


def fail(msg: str) -> None:
    problems.append(msg)


# ---------------------------------------------------------------- the map and the cycles
def g(y: int) -> int:
    return y // 2 if y % 2 == 0 else (3 * y - 1) // 2


def cycle_stats(start: int) -> tuple[int, int, int]:
    """(K, o, m) of the cycle through ``start``."""
    y, K, o = start, 0, 0
    minima = 0
    seq = []
    while True:
        seq.append(y)
        if y % 2:
            o += 1
        y = g(y)
        K += 1
        if y == start:
            break
    for i, v in enumerate(seq):
        if v % 2 and seq[i - 1] % 2 == 0:
            minima += 1
    return K, o, minima


# ---------------------------------------------------------------- continued fraction of x
def convergent_denominators(count: int = 60) -> list[int]:
    a = []
    t = X
    for _ in range(count):
        q = int(mp.floor(t))
        a.append(q)
        frac = t - q
        if frac == 0:
            break
        t = 1 / frac
    qs = [1, a[1]] if len(a) > 1 else [1]
    for k in range(2, len(a)):
        qs.append(a[k] * qs[-1] + qs[-2])
    return qs


# ---------------------------------------------------------------- the sieve
def sieve(eps: mp.mpf, kmax: int, Q: int) -> list[int]:
    """All 1 <= K <= kmax with 1 - {K x} < eps, by K = iQ + j.

    Integer arithmetic at 2^256 scale: the error in {Kx} is below K * 2^-256,
    negligible against the windows used here (never below 1e-15)."""
    P = (Q * XS + S // 2) // S
    Th = Q * XS - P * S
    E = int(mp.floor(eps * S))
    imax = kmax // Q
    hits: list[int] = []
    phi = 0
    t_lo, t_hi = min(0, imax * Th), max(0, imax * Th)
    for j in range(Q):
        n_lo = (phi + t_lo) // S
        n_hi = (phi + t_hi) // S
        for n in range(n_lo, n_hi + 1):
            A = n * S + S - E - phi
            Bd = n * S + S - phi
            if Th > 0:
                i_lo, i_hi = A // Th + 1, (Bd - 1) // Th
            else:
                i_lo, i_hi = (-Bd) // (-Th) + 1, (-A - 1) // (-Th)
            i_lo = max(i_lo, 1 if j == 0 else 0)
            i_hi = min(i_hi, imax)
            for i in range(i_lo, i_hi + 1):
                K = i * Q + j
                if 1 <= K <= kmax:
                    hits.append(K)
        phi = (phi + XS) % S
    return sorted(set(hits))


def direct_scan(eps: mp.mpf, kmax: int) -> list[int]:
    E = int(mp.floor(eps * S))
    return [K for K in range(1, kmax + 1) if (K * XS) % S > S - E]


def one_minus_frac(K: int) -> mp.mpf:
    kx = K * X
    return mp.ceil(kx) - kx


# ---------------------------------------------------------------- the inequalities
def B(m: int) -> mp.mpf:
    return (DELTA ** m - 1) / (DELTA - 1)


def L_min(K: int, m: int) -> mp.mpf:
    b = B(m)
    return (mp.mpf(K) / DELTA + (b - m) / (DELTA - 1)) / b


def f_ceiling(K: int, m: int) -> mp.mpf:
    return L_min(K, m) - RHIN * mp.log(K, 2) - mp.log(2 * m, 2)


def K3(m: int) -> int:
    """Least integer beyond which 2^L_min >= 2m K^13.3, from the convex shape."""
    kstar = RHIN * DELTA * B(m) / LN2
    lo = int(mp.ceil(kstar))
    if not f_ceiling(lo, m) < 0:
        raise AssertionError(f"f is not negative at its minimum for m={m}")
    hi = lo
    while f_ceiling(hi, m) < 0:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f_ceiling(mid, m) >= 0:
            hi = mid
        else:
            lo = mid
    if not (f_ceiling(hi, m) >= 0 and f_ceiling(hi - 1, m) < 0 and hi - 1 >= kstar):
        raise AssertionError(f"ceiling bracket failed for m={m}")
    return hi


def lam(K: int) -> tuple[int, mp.mpf]:
    o = int(mp.ceil(K * X))
    return o, o * LN3 - K * LN2


def margin(K: int, m: int) -> mp.mpf:
    _, L = lam(K)
    return mp.log(m / L, 2) - L_min(K, m)


# ---------------------------------------------------------------- the manuscript
def parse_note(text: str) -> dict:
    rows1, rows2 = [], []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) == 6 and cells[0].isdigit() and "cdot10^" in cells[1]:
            mant, expo = re.match(r"\\\((\d\.\d)\\cdot10\^\{(-?\d+)\}\\\)", cells[1]).groups()
            adm = int(cells[3])
            least = None if cells[4] == "—" else int(cells[4])
            marg = None if cells[5] == "—" else float(re.match(r"\\\(([+-]?\d+\.\d)\\\)", cells[5]).group(1))
            rows1.append({"m": int(cells[0]), "lambda_bound": (mant, int(expo)), "K3": int(cells[2]),
                          "admissible": adm, "least": least, "margin": marg})
        elif len(cells) == 4 and cells[0].startswith("\\(") and re.search(r"2\^\{\d+\}", cells[0]):
            if "301" in cells[0]:
                floor_key, floor = "301*2^50", 301 * 2 ** 50
            else:
                e = int(re.search(r"2\^\{(\d+)\}", cells[0]).group(1))
                floor_key, floor = f"2^{e}", 2 ** e
            rows2.append({"floor_key": floor_key, "floor": floor, "excluded_through": int(cells[1]),
                          "first_open": int(cells[2]),
                          "survivors": [int(s) for s in re.findall(r"\d+", cells[3])]})
    out = {"table1": rows1, "table2": rows2}
    out["abstract_closest_bits"] = float(re.search(r"the closest by \\\((\d+\.\d)\\\) bits", text).group(1))
    out["section5_closest_bits"] = float(re.search(r"hangs on \\\((\d+\.\d)\\\) bits at \\\(K=(\d+)\\\)", text).group(1))
    out["section5_closest_K"] = int(re.search(r"hangs on \\\((\d+\.\d)\\\) bits at \\\(K=(\d+)\\\)", text).group(2))
    out["abstract_floor_claims"] = [(int(a), int(b)) for a, b in
                                    re.findall(r"\\\(m\\le(\d+)\\\)\s+from\s+\\\(2\^\{(\d+)\}\\\)", text)]
    out["m_le_all_excluded"] = sorted({int(v) for v in re.findall(r"1\\le m\\le(\d+)", text)})
    out["title_M"] = int(re.search(r'title: "No m-cycles of the 3n−1 map for m ≤ (\d+)"', text).group(1))
    out["no_admissible_through"] = sorted({int(v) for v in re.findall(
        r"For \\\(m\\le(\d+)\\\)\s+(?:no\s+admissible|there is no admissible)", text)})
    out["first_admissible_m"] = int(re.search(r"for \\\((\d+)\\le m\\le\d+\\\) the admissible", text).group(1))
    block = re.search(r"leaves four lengths,\s*\\\[\s*(.+?)\s*\\\]", text, re.S).group(1)
    out["m50_lengths"] = [int(s) for s in re.findall(r"\d+", block)]
    out["m50_bits"] = [float(v) for v in re.search(
        r"with \\\((\d+\.\d)\\\), \\\((\d+\.\d)\\\), \\\((\d+\.\d)\\\) and \\\((\d+\.\d)\\\) bits of room", text).groups()]
    out["tightness"] = re.search(r"16\^\{\\delta\}/2=(\d+\.\d)", text).group(1)
    out["cycle_steps"] = re.search(r"\\\(\(K,o\)=\(1,1\),\(3,2\),\(11,7\)\\\)", text) is not None
    out["floor_odd_starts"] = int(re.search(r"\\\((\d+)\\\) odd starts counted exactly", text).group(1))
    out["floor_max_steps"] = sorted({int(v) for v in re.findall(r"greatest step\s+count \\\((\d+)\\\)", text)})
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--note", type=Path, default=NOTE)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    text = args.note.read_text(encoding="utf-8")
    note = parse_note(text)
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    report: dict = {"scope": __doc__.strip().splitlines()[0],
                    "note": str(args.note.relative_to(ROOT)) if args.note.is_relative_to(ROOT) else str(args.note)}

    # 1. the cycles
    cyc = {s: cycle_stats(s) for s in (1, 5, 17)}
    report["cycles"] = {str(k): v for k, v in cyc.items()}
    if not (cyc[1][:2] == (1, 1) and cyc[5][:2] == (3, 2) and cyc[17][:2] == (11, 7) and note["cycle_steps"]):
        fail(f"cycle steps: recomputed {cyc}, note states (1,1),(3,2),(11,7)")
    if cyc[5][2] != 1 or cyc[17][2] != 2:
        fail(f"m of the known cycles: {cyc}")
    t = mp.mpf(16) ** DELTA / 2
    report["tightness_16_delta_over_2"] = mp.nstr(t, 12)
    if abs(t - mp.mpf("40.5")) > mp.mpf("1e-90") or note["tightness"] != "40.5":
        fail(f"16^delta/2 = {mp.nstr(t, 15)}, note says {note['tightness']}")

    # 2. the sieve against a direct scan (coarse window), one convergent and one arbitrary modulus
    qs = convergent_denominators()
    for eps, kmax, Q in ((mp.mpf(1) / 500, 100_000, 306), (mp.mpf(1) / 700, 60_000, 1000)):
        a, b = sieve(eps, kmax, Q), direct_scan(eps, kmax)
        if a != b:
            fail(f"sieve disagrees with the direct scan at eps={eps}, kmax={kmax}, Q={Q}")
        report.setdefault("sieve_selftests", []).append({"eps": str(eps), "kmax": kmax, "Q": Q, "hits": len(b),
                                                         "agree": a == b})

    # 3. the ceilings, independently
    ceilings = {m: K3(m) for m in list(range(1, 51)) + [64, 69, 83]}
    report["K3"] = {str(m): v for m, v in ceilings.items()}
    for floor_key, table in summary["tables"].items():
        for r in table["rows"]:
            if r["m"] in ceilings and r["K3_rhin_ceiling"] != ceilings[r["m"]]:
                fail(f"K3({r['m']}) recomputed {ceilings[r['m']]} vs probe {r['K3_rhin_ceiling']} ({floor_key})")
    for r in note["table1"]:
        if r["K3"] != ceilings[r["m"]]:
            fail(f"Table 1 K3({r['m']}) = {r['K3']} vs recomputed {ceilings[r['m']]}")

    # 4. the admissible lengths at 2^40, 2^44, 2^48 through m = 50, by the sieve
    kmax = ceilings[50]
    eps_max = mp.mpf(50) / ((2 ** 40 - 1) * LN3)
    Q = max(q for q in qs if q * q <= 4 * kmax)
    hits = sieve(eps_max, kmax, Q)
    detail = {K: (lam(K), one_minus_frac(K)) for K in hits}
    for K, ((o, L), omf) in detail.items():
        if abs(L - LN3 * omf) > mp.mpf("1e-80") or not (0 < omf < eps_max):
            fail(f"inconsistent window arithmetic at K={K}")
        if min(omf, eps_max - omf) < mp.mpf("1e-30"):
            fail(f"K={K} within 1e-30 of a window boundary; the sieve's scale does not settle it")
    report["sieve"] = {"Q": Q, "kmax": kmax, "eps_max": mp.nstr(eps_max, 12), "hits": len(hits)}

    def rows_for(floor: int):
        rows = {}
        for m in range(1, 51):
            eps = mp.mpf(m) / ((floor - 1) * LN3)
            adm = [K for K in hits if K < ceilings[m] and detail[K][1] < eps]
            margins = {K: margin(K, m) for K in adm}
            surv = [K for K in adm if margins[K] > 0]
            rows[m] = {"admissible": adm, "least": adm[0] if adm else None,
                       "margin": max(margins.values()) if adm else None, "survivors": surv,
                       "survivor_bits": [margins[K] for K in surv]}
        return rows

    computed = {f: rows_for(f) for f in (2 ** 40, 2 ** 44, 2 ** 48)}
    report["floors"] = {}
    for floor, rows in computed.items():
        M = 0
        while M + 1 <= 50 and not rows[M + 1]["survivors"]:
            M += 1
        first_open = M + 1 if M < 50 else None
        report["floors"][f"2^{floor.bit_length() - 1}"] = {
            "excluded_through": M, "first_open": first_open,
            "first_open_survivors": [(K, mp.nstr(b, 6)) for K, b in
                                     zip(rows[first_open]["survivors"], rows[first_open]["survivor_bits"])] if first_open else [],
            "no_admissible_through": max([m for m in range(1, 51) if all(not rows[k]["admissible"] for k in range(1, m + 1))] or [0])}
        key = f"2^{floor.bit_length() - 1}"
        probe = summary["tables"][key]
        if probe["excluded_through"] != M:
            fail(f"{key}: excluded through {M} recomputed vs probe {probe['excluded_through']}")
        for r in probe["rows"]:
            m = r["m"]
            if m > 50:
                continue
            mine = rows[m]
            if r["admissible_count"] != len(mine["admissible"]) or r["K0_least_admissible"] != mine["least"]:
                fail(f"{key} m={m}: admissible {len(mine['admissible'])} least {mine['least']} vs probe "
                     f"{r['admissible_count']} / {r['K0_least_admissible']}")
            if [s["K"] for s in r["survivors"]] != mine["survivors"]:
                fail(f"{key} m={m}: survivors {mine['survivors']} vs probe {[s['K'] for s in r['survivors']]}")
            if mine["margin"] is not None and abs(float(mine["margin"]) - r["closest_slack_bits"]) > 1e-6:
                fail(f"{key} m={m}: margin {float(mine['margin'])} vs probe {r['closest_slack_bits']}")

    # 5. Table 1 (floor 2^44) against the recomputation
    rows44 = computed[2 ** 44]
    for r in note["table1"]:
        m, mine = r["m"], rows44[r["m"]]
        want = f"{float(mp.mpf(m) / (2 ** 44 - 1)):.1e}"
        mant, expo = want.split("e")
        if (mant, int(expo)) != r["lambda_bound"]:
            fail(f"Table 1 m={m}: m/(X0-1) prints {r['lambda_bound']} vs {want}")
        if r["admissible"] != len(mine["admissible"]) or r["least"] != mine["least"]:
            fail(f"Table 1 m={m}: admissible {r['admissible']}, least {r['least']} vs recomputed "
                 f"{len(mine['admissible'])}, {mine['least']}")
        if (r["margin"] is None) != (mine["margin"] is None) or (
                r["margin"] is not None and abs(r["margin"] - float(mine["margin"])) > 0.051):
            fail(f"Table 1 m={m}: margin {r['margin']} vs recomputed {mine['margin']}")
    M44 = report["floors"]["2^44"]["excluded_through"]
    if not (note["title_M"] == M44 and note["m_le_all_excluded"] == [M44]):
        fail(f"the theorem's M: title {note['title_M']}, text {note['m_le_all_excluded']}, recomputed {M44}")
    if note["no_admissible_through"] != [report["floors"]["2^44"]["no_admissible_through"]]:
        fail(f"'no admissible length' bound: note {note['no_admissible_through']} vs "
             f"recomputed {report['floors']['2^44']['no_admissible_through']}")
    if note["first_admissible_m"] != report["floors"]["2^44"]["no_admissible_through"] + 1:
        fail(f"first m with an admissible length: note {note['first_admissible_m']}")
    closest = rows44[M44]
    if abs(note["abstract_closest_bits"] + float(closest["margin"])) > 0.051 or \
            abs(note["section5_closest_bits"] + float(closest["margin"])) > 0.051:
        fail(f"closest margin at m={M44}: note {note['abstract_closest_bits']} vs {closest['margin']}")
    worst_K = max(closest["admissible"], key=lambda K: margin(K, M44))
    if note["section5_closest_K"] != worst_K:
        fail(f"closest length at m={M44}: note {note['section5_closest_K']} vs {worst_K}")
    open44 = rows44[M44 + 1]
    if note["m50_lengths"] != open44["survivors"] or any(
            abs(a - float(b)) > 0.051 for a, b in zip(note["m50_bits"], open44["survivor_bits"])):
        fail(f"m={M44 + 1} survivors: note {note['m50_lengths']} {note['m50_bits']} vs "
             f"{open44['survivors']} {[float(b) for b in open44['survivor_bits']]}")

    # 6. Table 2 and the abstract's floor claims
    for r in note["table2"]:
        key = r["floor_key"]
        probe = summary["tables"][key]
        if r["floor"] in computed:
            got = report["floors"][key]
            if (got["excluded_through"], got["first_open"]) != (r["excluded_through"], r["first_open"]) or \
                    [K for K, _ in got["first_open_survivors"]] != r["survivors"]:
                fail(f"Table 2 {key}: note {r} vs recomputed {got}")
        else:
            if probe["excluded_through"] != r["excluded_through"]:
                fail(f"Table 2 {key}: excluded through {r['excluded_through']} vs probe {probe['excluded_through']}")
            first = next(x for x in probe["rows"] if not x["excluded"])
            if first["m"] != r["first_open"] or [s["K"] for s in first["survivors"]] != r["survivors"]:
                fail(f"Table 2 {key}: first open row differs from the probe")
            m = r["first_open"]
            eps = mp.mpf(m) / ((r["floor"] - 1) * LN3)
            for K in r["survivors"]:
                omf = one_minus_frac(K)
                if not (omf < eps and K < ceilings[m] and margin(K, m) > 0):
                    fail(f"Table 2 {key}: printed survivor {K} is not admissible with a positive margin")
            report["floors"][key] = {"checked": "printed survivors only", "first_open": m,
                                     "survivor_bits": [mp.nstr(margin(K, m), 6) for K in r["survivors"]]}
    claims = {f"2^{e}": M for M, e in note["abstract_floor_claims"]}
    if len(claims) != 3:
        fail(f"abstract floor claims not parsed as three: {note['abstract_floor_claims']}")
    for key, M in claims.items():
        entry = report["floors"].get(key, {})
        got = entry["excluded_through"] if "excluded_through" in entry \
            else summary["tables"].get(key, {}).get("excluded_through")
        if got != M:
            fail(f"abstract: m <= {M} from {key} vs {got}")

    # 7. the floor certificate's printed numbers, where a record exists
    cert_dir = ROOT / "data/research/juggler/negative_floor_3x1"
    found = {"odd_starts": None, "max_steps": {str(v): None for v in note["floor_max_steps"]}}

    def max_steps_values(obj, under=False) -> set:
        vals = set()
        if isinstance(obj, dict):
            for k, v in obj.items():
                vals |= max_steps_values(v, under or str(k).startswith("max_steps"))
        elif isinstance(obj, list):
            for v in obj:
                vals |= max_steps_values(v, under)
        elif under and isinstance(obj, int):
            vals.add(obj)
        return vals

    for p in sorted(cert_dir.glob("*.json")) if cert_dir.is_dir() else []:
        blob = p.read_text(encoding="utf-8", errors="replace")
        if str(note["floor_odd_starts"]) in blob:
            found["odd_starts"] = p.name
        try:
            recorded = max_steps_values(json.loads(blob))
        except json.JSONDecodeError:
            recorded = set()
        for v in note["floor_max_steps"]:
            if v in recorded:
                found["max_steps"][str(v)] = p.name
    if any(v is None for v in found["max_steps"].values()):
        fail(f"a greatest step count in the note is not a max_steps entry of the certificate: {found['max_steps']}")
    report["floor_certificate_numbers"] = {"note": {"odd_starts": note["floor_odd_starts"],
                                                    "max_steps": note["floor_max_steps"]}, "found_in": found,
                                           "scope": "presence in the certificate's records only; the certificate "
                                                    "itself is not re-run here"}
    if found["odd_starts"] is None:
        fail(f"the odd-start count {note['floor_odd_starts']} is not in any certificate record under {cert_dir}")

    report["problems"] = problems
    report["passed"] = not problems
    args.output.write_text(json.dumps(report, indent=1) + "\n", encoding="utf-8")
    if problems:
        print("MANUSCRIPT CHECK FAILED")
        for p in problems:
            print(" -", p)
        return 1
    print(f"manuscript check passed: {len(hits)} admissible lengths sieved below {kmax}, "
          f"{len(ceilings)} ceilings, tables agree; report at {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
