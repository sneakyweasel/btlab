"""Second OO from an odd cube-corridor landing.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a bunched-short tail table, not a leftover-suffix path, not Z5,
not a length-11 assembler, and not a four-even leftover cell.

After an odd OOEOOOE landing, the forced next O produces an odd
q in [n^2, n^3) carrying q^{256} <= n^{729}. Phase 0 asks what
exact corridor the next OO occupies, using that envelope rather
than a generic q < n^3 bound.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLE_CORE,
    ENVELOPE,
    JUGGLER_PAPER_BARREL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import square_cell_gap
from research.juggler_sequence.odd_oooe_next import odd_oooe_next
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_oo_cube.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_second_oo_cube.md"

CLASS_GREEN = "SECOND_OO_GREEN"
CLASS_PARK = "SECOND_OO_PARK"
CLASS_CLOSE = "SECOND_OO_CLOSE"
CLASS_REMAINS = "SECOND_OO_REMAINS"
CLASS_INCOMPLETE = "SECOND_OO_INCOMPLETE"

N_MIN = 12
N_HI = 801
GRAPH_HI = 2001

# q^{256} <= n^{729} and u^2 <= q^3 give u^{512} <= n^{2187}.
U_NUM = 2187
U_DEN = 512
# u odd: v^2 <= u^3 gives v^{1024} <= n^{6561}.
V_NUM = 6561
V_DEN = 1024
# even u: s = isqrt(u) satisfies s^{1024} <= n^{2187}.
S_NUM = 2187
S_DEN = 1024

# q odd, u even, s odd in C_2: second OOO from s.
EVEN_U_OOO = {"n": 491, "w": 128423, "q": 46021865, "u": 312209649122, "s": 558757}
# q odd, u even, s even: next E returns to C_1 without dropping.
EVEN_U_C1 = {
    "n": 501,
    "w": 133347,
    "q": 48693935,
    "u": 339791341082,
    "s": 582916,
    "t": 763,
}
# q odd, u odd: second OO continues to v in the 6561/1024 band.
ODD_U = {
    "n": 1181,
    "w": 679765,
    "q": 560451711,
    "u": 13268056096991,
    "v": 48329349373548636613,
}
# Even-q contrast, not a second OO from odd q.
CONTRAST_EVEN_Q = {"n": 483, "w": 124381, "q": 43866306, "r": 6623}

LEAN_THEOREMS = (
    "CycleMin",
    "power_bound_word",
    "power_bound_contracts",
    "ooo_residual_ge_cube",
    "no_cycleMin_ooeoooe",
    "floorPower_oooee_five_step_lt",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eleven",
    "no_cycleMin_four_even",
    "no_cycleMin_five_even",
    "no_juggler_cycle",
)


def scale_band(x: int, n: int) -> int:
    """Largest k with n^k <= x. Band C_k is [n^k, n^{k+1})."""
    if n < 2 or x < 1:
        raise ValueError("scale_band needs n >= 2 and x >= 1")
    if x < n:
        return 0
    k = 0
    p = 1
    while p <= x // n:
        p *= n
        k += 1
    return k


def u_lt_fifth() -> bool:
    """u^{512} <= n^{2187} < n^{2560} = (n^5)^{512}."""
    return U_NUM < 5 * U_DEN


def u_lt_fourth() -> bool:
    """2187 < 2048 fails, so u < n^4 is not inherited."""
    return U_NUM < 4 * U_DEN


def u_inherited_lt_generic() -> bool:
    """Generic q < n^3 gives u < n^{9/2}; 2187 < 2304."""
    return U_NUM < (9 * U_DEN) // 2


def v_lt_seventh() -> bool:
    """v^{1024} <= n^{6561} < n^{7168} = (n^7)^{1024}."""
    return V_NUM < 7 * V_DEN


def v_lt_sixth() -> bool:
    """6561 < 6144 fails, so v < n^6 is not inherited."""
    return V_NUM < 6 * V_DEN


def v_inherited_lt_generic() -> bool:
    """Generic q < n^3 then two O steps give v < n^{27/4}; 6561 < 6912."""
    return V_NUM < (27 * V_DEN) // 4


def s_lt_square() -> bool:
    """Even-u landing s^{1024} <= n^{2187} does not force s < n^2."""
    return S_NUM < 2 * S_DEN


def t_lt_n() -> bool:
    """OOEOOOEOOEE has 7 odds and length 11: 2187 < 2048 fails."""
    return 3**7 < 2**11


def word_gaps() -> dict[str, bool]:
    return {
        "OOEOOOEOO": square_cell_gap(9, 7),
        "OOEOOOEOOE": square_cell_gap(10, 7),
        "OOEOOOEOOEE": square_cell_gap(11, 7),
        "u_lt_n5": u_lt_fifth(),
        "u_lt_n4": u_lt_fourth(),
        "u_sharper": u_inherited_lt_generic(),
        "v_lt_n7": v_lt_seventh(),
        "v_lt_n6": v_lt_sixth(),
        "v_sharper": v_inherited_lt_generic(),
        "s_lt_n2": s_lt_square(),
        "t_lt_n": t_lt_n(),
        "ooeoooeeooee_contracts": t_lt_n(),
    }


def second_oo(n: int) -> dict[str, Any] | None:
    """Next OO after an inherited odd cube-corridor q."""
    row = odd_oooe_next(n)
    if row is None or row["branch"] != "odd_q":
        return None
    if not row["w_lt_sq"] or not row["q_lt_cube"] or not row["w_ge_n"]:
        return None
    w = row["w"]
    q = row["q"]
    u = row["t2"]
    n3 = n**3
    out: dict[str, Any] = {
        "n": n,
        "w": w,
        "q": q,
        "u": u,
        "d0": w**3 - q * q,
        "d1": q**3 - u * u,
        "w_band": scale_band(w, n),
        "q_band": scale_band(q, n),
        "u_band": scale_band(u, n),
        "u_even": u % 2 == 0,
        "u_ge_n3": u >= n3,
        "u_lt_n5": u < n**5,
        "q_ge_sq": q >= n * n,
        "q_lt_cube": q < n3,
        "w_lt_sq": True,
    }
    if u % 2 == 0:
        s = floor_power(u)
        out["branch"] = "even_u"
        out["s"] = s
        out["s_even"] = s % 2 == 0
        out["s_band"] = scale_band(s, n)
        out["s_lt_n2"] = s < n * n
        out["s_ge_three_halves"] = s * s >= n3
        if s % 2 == 0:
            t = floor_power(s)
            out["t"] = t
            out["t_band"] = scale_band(t, n)
            out["drop"] = t < n
            out["first"] = "even_even_c1" if t >= n else "even_even_drop"
        else:
            out["first"] = "even_odd_OOO"
    else:
        v = floor_power(u)
        out["branch"] = "odd_u"
        out["v"] = v
        out["d2"] = u**3 - v * v
        out["v_even"] = v % 2 == 0
        out["v_band"] = scale_band(v, n)
        out["v_lt_n7"] = v < n**7
        out["v_ge_nine_halves"] = v * v >= n**9
        out["first"] = "odd_OOE" if v % 2 == 0 else "odd_OOO"
    return out


def witness_row(n: int) -> dict[str, Any]:
    row = second_oo(n)
    if row is None:
        return {"n": n, "missing": True}
    return {
        "n": n,
        "w": row["w"],
        "q": row["q"],
        "u": row["u"],
        "branch": row["branch"],
        "first": row["first"],
        "u_ge_n3": row["u_ge_n3"],
        "u_lt_n5": row["u_lt_n5"],
        "u_band": row["u_band"],
        "s": row.get("s"),
        "s_even": row.get("s_even"),
        "s_lt_n2": row.get("s_lt_n2"),
        "t": row.get("t"),
        "t_band": row.get("t_band"),
        "drop": row.get("drop"),
        "v": row.get("v"),
        "v_even": row.get("v_even"),
        "v_band": row.get("v_band"),
        "v_lt_n7": row.get("v_lt_n7"),
        "v_ge_nine_halves": row.get("v_ge_nine_halves"),
    }


def _edge_label(row: dict[str, Any]) -> str:
    if row["branch"] == "even_u":
        return row["first"]
    return "odd_u_" + row["first"]


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    firsts: Counter[str] = Counter()
    u_fail = 0
    v_fail = 0
    s_fail = 0
    d0_fracs: list[float] = []
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = second_oo(n)
        if row is None:
            continue
        firsts[row["first"]] += 1
        if not row["u_ge_n3"] or not row["u_lt_n5"]:
            u_fail += 1
        d0_fracs.append(row["d0"] / (2 * row["q"]))
        if row["branch"] == "even_u":
            if not row["s_ge_three_halves"]:
                s_fail += 1
        else:
            if not row["v_lt_n7"] or not row["v_ge_nine_halves"]:
                v_fail += 1
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "branch": row["branch"],
                    "first": row["first"],
                    "u_band": row["u_band"],
                    "u_lt_n5": row["u_lt_n5"],
                }
            )
    return {
        "n_hi": n_hi,
        "firsts": {k: v for k, v in firsts.most_common()},
        "u_fail": u_fail,
        "v_fail": v_fail,
        "s_fail": s_fail,
        "d0_frac_min": min(d0_fracs) if d0_fracs else None,
        "d0_frac_max": max(d0_fracs) if d0_fracs else None,
        "samples": samples,
    }


def scan_graph(n_hi: int = GRAPH_HI) -> dict[str, Any]:
    edges: Counter[str] = Counter()
    u_bands: Counter[int] = Counter()
    transitions: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = second_oo(n)
        if row is None:
            continue
        edges[_edge_label(row)] += 1
        u_bands[row["u_band"]] += 1
        item = {
            "n": n,
            "edge": _edge_label(row),
            "w_band": row["w_band"],
            "q_band": row["q_band"],
            "u_band": row["u_band"],
            "u_even": row["u_even"],
        }
        if row["branch"] == "even_u":
            item["s_band"] = row["s_band"]
            item["s_even"] = row["s_even"]
            if "t_band" in row:
                item["t_band"] = row["t_band"]
                item["drop"] = row["drop"]
        else:
            item["v_band"] = row["v_band"]
            item["v_even"] = row["v_even"]
        transitions.append(item)
    return {
        "n_hi": n_hi,
        "edges": {k: v for k, v in edges.most_common()},
        "u_bands": {str(k): v for k, v in sorted(u_bands.items())},
        "c1_return": any(
            item.get("t_band") == 1 and item.get("drop") is False
            for item in transitions
        ),
        "transitions": transitions,
    }


def family_rows() -> dict[str, Any]:
    """483 / 491 / 501 / 1181 in the scale-band language."""
    even_q = odd_oooe_next(CONTRAST_EVEN_Q["n"])
    assert even_q is not None
    r = even_q["r"]
    n = CONTRAST_EVEN_Q["n"]
    return {
        "contrast_483": {
            "n": n,
            "w": even_q["w"],
            "q": even_q["q"],
            "t_q": r,
            "t2_q": floor_power(r),
            "w_band": scale_band(even_q["w"], n),
            "q_band": scale_band(even_q["q"], n),
            "t_q_band": scale_band(r, n),
            "q_even": True,
            "note": "even_q OE, not a second OO from odd q",
        },
        "odd_491": witness_row(EVEN_U_OOO["n"]),
        "odd_501": witness_row(EVEN_U_C1["n"]),
        "odd_1181": witness_row(ODD_U["n"]),
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "graph_hi": GRAPH_HI,
        "exponents_ok": u_lt_fifth() and v_lt_seventh() and u_inherited_lt_generic(),
        "u_sharper": u_inherited_lt_generic(),
        "v_sharper": v_inherited_lt_generic(),
        "gaps": word_gaps(),
        "window": scan_window(),
        "graph": scan_graph(),
        "even_u_ooo": witness_row(EVEN_U_OOO["n"]),
        "even_u_c1": witness_row(EVEN_U_C1["n"]),
        "odd_u": witness_row(ODD_U["n"]),
        "family": family_rows(),
        "length_eleven_census": False,
        "z5_cells": False,
        "four_even_assembler": False,
        "leftover_suffix_retest": False,
        "terminal_cluster_reopen": False,
        "residue_automaton": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if CYCLE_CORE.is_file():
        combined += CYCLE_CORE.read_text(encoding="utf-8")
    if ENVELOPE.is_file():
        combined += ENVELOPE.read_text(encoding="utf-8")
    if CELLS.is_file():
        combined += CELLS.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "not_in_paper_barrel": "SecondOoCube" not in paper,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_lean": True,
    }


def _witnesses_ok(scan: dict[str, Any]) -> bool:
    ooo = scan["even_u_ooo"]
    c1 = scan["even_u_c1"]
    odd = scan["odd_u"]
    return (
        ooo.get("first") == "even_odd_OOO"
        and ooo.get("q") == EVEN_U_OOO["q"]
        and ooo.get("u") == EVEN_U_OOO["u"]
        and ooo.get("s") == EVEN_U_OOO["s"]
        and ooo.get("s_even") is False
        and ooo.get("s_lt_n2") is False
        and ooo.get("u_ge_n3")
        and ooo.get("u_lt_n5")
        and c1.get("first") == "even_even_c1"
        and c1.get("q") == EVEN_U_C1["q"]
        and c1.get("s") == EVEN_U_C1["s"]
        and c1.get("t") == EVEN_U_C1["t"]
        and c1.get("drop") is False
        and c1.get("t_band") == 1
        and odd.get("first") == "odd_OOO"
        and odd.get("q") == ODD_U["q"]
        and odd.get("u") == ODD_U["u"]
        and odd.get("v") == ODD_U["v"]
        and odd.get("v_even") is False
        and odd.get("v_lt_n7")
        and odd.get("v_ge_nine_halves")
    )


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["power_bound_word"]
        and lean["no_cycleMin_ooeoooe"]
        and not lean["has_no_cycle_itinerary_length_eleven"]
        and not lean["has_no_cycleMin_four_even"]
        and not lean["has_no_juggler_cycle"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["four_even_assembler"]
        or scan["leftover_suffix_retest"]
        or scan["terminal_cluster_reopen"]
        or scan["residue_automaton"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    gaps = scan["gaps"]
    if (
        not scan["exponents_ok"]
        or not scan["u_sharper"]
        or not scan["v_sharper"]
        or not gaps["u_lt_n5"]
        or gaps["u_lt_n4"]
        or not gaps["v_lt_n7"]
        or gaps["v_lt_n6"]
        or gaps["s_lt_n2"]
        or gaps["t_lt_n"]
        or gaps["OOEOOOEOO"]
        or not gaps["OOEOOOEOOEE"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an exact second-OO comparison failed",
        }
    window = scan["window"]
    graph = scan["graph"]
    if window["u_fail"] or window["v_fail"] or window["s_fail"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a second-OO corridor failed in the window",
        }
    if not graph["c1_return"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "the C_1 return type is missing",
        }
    if not _witnesses_ok(scan):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "named second-OO witnesses failed",
        }
    if not window["firsts"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no inherited odd-q second OO in the window",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "odd q from OOEOOOE carries q^{256} <= n^{729} into the "
            "next OO: n^3 <= T(q) < n^{2187/512}; even T(q) lands in "
            "[n^{3/2}, n^{2187/1024}); odd T(q) continues with "
            "T^2(q)^{1024} <= n^{6561}. Sharper than generic 3/2. "
            "The scale graph returns to C_1 (501)"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "length_eleven_census": False,
            "z5_cells": False,
            "four_even_assembler": False,
            "second_oo_in_c2_c3": False,
            "scale_automaton_acyclic": False,
            "even_u_always_drops": False,
            "defect_chain_constrained": False,
        }
    )
    return {
        "experiment": "juggler_second_oo_cube",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "inherited odd cube-corridor q only; raise 729/256 "
            "through one or two O steps; 2187 < 2560 and 6561 < 7168; "
            "no terminal cell, no residue automaton, no Z5, no length-11"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    graph = scan["graph"]
    lines = [
        "# Juggler second OO from the cube corridor",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The second OO after an odd",
        "cube-corridor q from OOEOOOE. Not Z5, not a length-11",
        "assembler, and not a terminal-cluster reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     second OO from odd q in [n^2, n^3)",
        "Novelty hypothesis      inherited 729/256 beats generic 3/2",
        "Existing machinery      odd OOEOOOE cube corridor;",
        "                        729 < 768",
        "Maximum Phase-0 scope   raise 729/256 through OO;",
        "                        parity split; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- 2187 < 2560 and 6561 < 7168: `{scan['exponents_ok']}`",
        f"- inherited u / v sharper: `{scan['u_sharper']}` / `{scan['v_sharper']}`",
        f"- gaps: `{scan['gaps']}`",
        f"- first events: `{window['firsts']}`",
        f"- graph edges: `{graph['edges']}`",
        f"- C_1 return: `{graph['c1_return']}`",
        f"- u / v / s fail: `{window['u_fail']}` / `{window['v_fail']}` / `{window['s_fail']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — inherited envelopes",
        "",
        "`q^{256} <= n^{729}` and `u^2 <= q^3` give `u^{512} <= n^{2187}`.",
        "So `n^3 <= u < n^{2187/512}` (`2187 < 2560`, `2187 > 2048`).",
        "This is sharper than the generic `u < n^{9/2}` (`2187 < 2304`).",
        "If `u` is odd, `v^{1024} <= n^{6561}`, so",
        "`n^{9/2} <= v < n^{6561/1024}` (`6561 < 7168`, `6561 > 6144`,",
        "and `6561 < 6912` beats generic `n^{27/4}`).",
        "",
        "## Attack 2 — parity after the first image",
        "",
        "Even `u` lands at `s` with `n^{3/2} <= s < n^{2187/1024}`.",
        "`s < n^2` is not forced (`2187 > 2048`). The word",
        "`OOEOOOEOOEE` does not contract versus `n` (`2187 > 2048`).",
        "Odd `u` continues the second `OO` into the `6561/1024` band.",
        "",
        "## Attack 3 — scale graph",
        "",
        "Observed inherited odd-`q` types: `C_1 --O--> C_2 --O--> C_4`,",
        "then even `u` to `C_2` or odd `u` to `C_6`. The even-even",
        "landing of `501` returns to `C_1` (`763`). The scale graph",
        "is not acyclic.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` branch=`{row['branch']}` "
                f"first=`{row['first']}` u-band=`{row['u_band']}`"
            )
        lines.append("")
    lines.append("## Named witnesses")
    lines.append("")
    for key in ("even_u_ooo", "even_u_c1", "odd_u"):
        row = scan[key]
        lines.append(
            f"- n=`{row['n']}` branch=`{row.get('branch')}` "
            f"first=`{row.get('first')}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(["", "## Anti-overclaim", ""])
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
            "This is not a halt result, not a Z5 exclusion, and not a",
            "length-11 assembler. Terminal clusters stay frozen.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    window = payload["scan"]["window"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"firsts={window['firsts']}")
    print(f"edges={payload['scan']['graph']['edges']}")


if __name__ == "__main__":
    main()
