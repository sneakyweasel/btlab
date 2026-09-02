"""Naive path-sum of existing local remainders versus word statistics.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not invent a new rho. Rho is Lean pathDefectSum / sum of
local_defect. Delta is the existing weighted globalDefect.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from research.juggler_sequence.global_defect import (
    follows_itinerary,
    image_after,
    local_defect,
    odd_count,
)
from research.juggler_sequence.lean_paths import (
    CYCLES,
    engine_floor_text,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.residual_chain import HARD_PROBES

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_sum_rho.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_sum_rho.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "sum_rho"
LEAN_PATH = CYCLES

CLASS_TELESCOPE = "RHO_TELESCOPE_GREEN"
CLASS_WORD = "RHO_WORD_BOUND_GREEN"
CLASS_DEFECT = "RHO_DEFECT_GREEN"
CLASS_COMPOSE = "RHO_COMPOSITION_GREEN"
CLASS_COUNTER = "RHO_COUNTEREXAMPLE"
CLASS_COMPLEX = "RHO_COMPLEX"
CLASS_REPACK = "RHO_REPACK"
CLASS_INCOMPLETE = "RHO_INCOMPLETE"

N_MAX = 4000
K_MAX = 20
DELTA_K_MAX = 8
BIT_LIMIT = 256
ALGORITHM_VERSION = "sum-rho-v1"
FIXED_WORDS = ("E", "O", "EE", "EO", "OE", "OO", "OOE", "OEO", "EOO", "OOOOE")
PE_STARTS = (365, 1999)

EXISTING_DEFS = (
    "pathDefectSum",
    "pathPows_eq_next_add_defects",
    "globalDefect",
    "localDefectEven",
    "localDefectOdd",
)


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    return value


def run_signature(word: str) -> tuple[int, int, int, int]:
    if not word:
        return (0, 0, 0, 0)
    runs = 1
    max_o = max_e = cur = 0
    last = word[0]
    for letter in word:
        if letter == last:
            cur += 1
        else:
            if last == "O":
                max_o = max(max_o, cur)
            else:
                max_e = max(max_e, cur)
            runs += 1
            last = letter
            cur = 1
    if last == "O":
        max_o = max(max_o, cur)
    else:
        max_e = max(max_e, cur)
    return (runs, max_o, max_e, word.find("EO") if "EO" in word else word.find("OE"))


def exponent_gap(k: int, o: int) -> int:
    return 3**o - (1 << k)


def path_pows_and_next_sq(states: list[int]) -> tuple[int, int]:
    pows = 0
    nxt = 0
    for i in range(len(states) - 1):
        x = states[i]
        pows += x if x % 2 == 0 else x * x * x
        nxt += states[i + 1] * states[i + 1]
    return pows, nxt


def walk(
    n: int,
    k_max: int = K_MAX,
    *,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    states = [n]
    rhos: list[int] = []
    letters: list[str] = []
    current = n
    overflow = False
    for _ in range(k_max):
        if current < 1 or current.bit_length() > bit_limit:
            overflow = True
            break
        letter = "E" if current % 2 == 0 else "O"
        rho = local_defect(current)
        y = floor_power(current)
        letters.append(letter)
        rhos.append(rho)
        current = y
        states.append(current)
        if current.bit_length() > bit_limit:
            overflow = True
            break
    word = "".join(letters)
    rho_sum = sum(rhos)
    k = len(word)
    o = odd_count(word)
    end = states[-1]
    delta = None
    surplus = None
    slack = None
    runs, max_o, max_e, first_mixed = run_signature(word)
    return {
        "n": n,
        "word": word,
        "k": k,
        "o": o,
        "end": end,
        "rho_sum": rho_sum,
        "rhos": rhos,
        "delta": delta,
        "surplus": surplus,
        "slack": slack,
        "gap": exponent_gap(k, o),
        "runs": runs,
        "max_O": max_o,
        "max_E": max_e,
        "first_mixed": first_mixed,
        "overflow": overflow,
        "states": states,
        "contracts": end < n,
        "expands": end > n,
    }


def prefixes(record: dict[str, Any]) -> list[dict[str, Any]]:
    n = record["n"]
    states = record["states"]
    rhos = record["rhos"]
    word = record["word"]
    out = []
    for k in range(1, len(word) + 1):
        y = states[k]
        piece = word[:k]
        o = odd_count(piece)
        runs, max_o, max_e, first_mixed = run_signature(piece)
        out.append(
            {
                "n": n,
                "word": piece,
                "k": k,
                "o": o,
                "end": y,
                "rho_sum": sum(rhos[:k]),
                "delta": None,
                "gap": exponent_gap(k, o),
                "runs": runs,
                "max_O": max_o,
                "max_E": max_e,
                "first_mixed": first_mixed,
                "contracts": y < n,
                "expands": y > n,
            }
        )
    return out


def identity_checks(record: dict[str, Any]) -> dict[str, bool]:
    from research.juggler_sequence.global_defect import envelope_slack, global_defect

    states = record["states"]
    rhos = record["rhos"]
    word = record["word"]
    n = record["n"]
    pows, nxt = path_pows_and_next_sq(states)
    add = True
    for split in range(len(word) + 1):
        u, v = word[:split], word[split:]
        mid = image_after(n, u) if u else n
        left = sum(rhos[:split])
        right = sum(local_defect(s) for s in _prefix_states(mid, v))
        if left + right != record["rho_sum"]:
            add = False
            break
    delta = global_defect(n, word)
    slack = envelope_slack(n, word)
    return {
        "path_identity": pows == nxt + record["rho_sum"],
        "compose_additive": add,
        "delta_eq_slack": delta == slack,
        "delta_ge_rho": delta >= record["rho_sum"],
        "one_step_eq": len(word) != 1 or delta == record["rho_sum"],
    }


def _prefix_states(start: int, word: str) -> list[int]:
    current = start
    out = []
    for letter in word:
        out.append(current)
        if (letter == "E") != (current % 2 == 0):
            break
        current = floor_power(current)
    return out


def collect_rows(*, n_max: int = N_MAX, k_max: int = K_MAX) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[tuple[int, str]] = set()
    for n in range(1, n_max + 1):
        rec = walk(n, k_max)
        for prefix in prefixes(rec):
            key = (prefix["n"], prefix["word"])
            if key in seen:
                continue
            seen.add(key)
            rows.append(prefix)
    extra = list(HARD_PROBES) + list(PE_STARTS)
    for n in extra:
        rec = walk(n, k_max)
        for prefix in prefixes(rec):
            key = (prefix["n"], prefix["word"])
            if key in seen:
                continue
            seen.add(key)
            rows.append(prefix)
    for word in FIXED_WORDS:
        for n in range(1, min(n_max, 800) + 1):
            if not follows_itinerary(n, word):
                continue
            rec = walk(n, len(word))
            if rec["word"] != word:
                continue
            key = (n, word)
            if key in seen:
                continue
            seen.add(key)
            rows.append(
                {
                    "n": n,
                    "word": word,
                    "k": rec["k"],
                    "o": rec["o"],
                    "end": rec["end"],
                    "rho_sum": rec["rho_sum"],
                    "delta": rec["delta"],
                    "gap": rec["gap"],
                    "runs": rec["runs"],
                    "max_O": rec["max_O"],
                    "max_E": rec["max_E"],
                    "first_mixed": rec["first_mixed"],
                    "contracts": rec["contracts"],
                    "expands": rec["expands"],
                }
            )
    return rows


def _min_pair(rows: list[dict[str, Any]], key: str) -> list[dict[str, Any]] | None:
    if len(rows) < 2:
        return None
    ordered = sorted(rows, key=lambda row: (row[key], row["n"], row["word"]))
    a, b = ordered[0], ordered[-1]
    if a[key] == b[key]:
        return None
    return [
        {"n": a["n"], "word": a["word"], key: a[key]},
        {"n": b["n"], "word": b["word"], key: b[key]},
    ]


def test_h1(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        groups[(row["k"], row["o"])].append(row)
    splits = []
    for (k, o), grp in groups.items():
        values = {row["rho_sum"] for row in grp}
        if len(values) > 1:
            pair = _min_pair(grp, "rho_sum")
            splits.append({"k": k, "o": o, "n_values": len(values), "pair": pair})
    splits.sort(key=lambda item: (item["k"], item["o"]))
    return {
        "holds": not splits,
        "n_groups": len(groups),
        "n_splits": len(splits),
        "first": splits[0] if splits else None,
    }


def test_h2(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Scale-aware candidates. Reject Delta-rewrites separately."""

    def cand_n3(row: dict[str, Any]) -> int:
        return row["k"] * (2 * row["n"] ** 3 + 1)

    def cand_start_window(row: dict[str, Any]) -> int:
        return row["k"] * (2 * max(row["n"], 1) + 1)

    out = {}
    for name, fn in (("k_times_2n3", cand_n3), ("k_times_2n", cand_start_window)):
        viol = None
        worst = None
        for row in rows:
            bound = fn(row)
            if bound <= 0:
                continue
            if row["rho_sum"] > bound:
                if viol is None or (row["n"], row["k"]) < (viol["n"], viol["k"]):
                    viol = {
                        "n": row["n"],
                        "k": row["k"],
                        "word": row["word"],
                        "rho_sum": row["rho_sum"],
                        "bound": bound,
                    }
            ratio = row["rho_sum"] / bound if bound else None
            if ratio is not None and (worst is None or ratio > worst["ratio"]):
                worst = {
                    "n": row["n"],
                    "word": row["word"],
                    "ratio": ratio,
                    "rho_sum": row["rho_sum"],
                    "bound": bound,
                }
        out[name] = {"holds": viol is None, "first_counterexample": viol, "worst_ratio": worst}
    return out


def test_h3(rows: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int, int, int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        groups[(row["k"], row["o"], row["runs"], row["max_O"], row["max_E"])].append(row)
    splits = []
    for key, grp in groups.items():
        values = {row["rho_sum"] for row in grp}
        if len(values) > 1:
            pair = _min_pair(grp, "rho_sum")
            splits.append(
                {
                    "k": key[0],
                    "o": key[1],
                    "runs": key[2],
                    "max_O": key[3],
                    "max_E": key[4],
                    "n_values": len(values),
                    "pair": pair,
                }
            )
    splits.sort(key=lambda item: (item["k"], item["o"], item["runs"]))
    return {
        "holds": not splits,
        "n_groups": len(groups),
        "n_splits": len(splits),
        "first": splits[0] if splits else None,
    }


def short_delta_rows(*, n_max: int = 200, k_max: int = 6) -> list[dict[str, Any]]:
    from research.juggler_sequence.global_defect import global_defect

    rows = []
    for n in range(1, n_max + 1):
        rec = walk(n, k_max)
        for k in range(1, rec["k"] + 1):
            word = rec["word"][:k]
            try:
                delta = global_defect(n, word)
            except (OverflowError, ValueError):
                continue
            rows.append(
                {
                    "n": n,
                    "word": word,
                    "k": k,
                    "o": odd_count(word),
                    "rho_sum": sum(rec["rhos"][:k]),
                    "delta": delta,
                    "gap": exponent_gap(k, odd_count(word)),
                    "end": rec["states"][k],
                    "contracts": rec["states"][k] < n,
                    "expands": rec["states"][k] > n,
                }
            )
    return rows


def test_h4(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Rho > |gap| or Rho > surplus as a contraction law.

    On expanding rows, surplus = n^{3^o}-n^{2^k} >= Delta >= Rho, so
    Rho > surplus cannot fire. Count that tautology explicitly.
    """

    if any(row.get("delta") is None for row in rows):
        rows = short_delta_rows()
    expanding = [row for row in rows if row["expands"]]
    contracting = [row for row in rows if row["contracts"]]
    fire_expand = 0
    for row in expanding:
        if row["rho_sum"] > row["delta"]:
            fire_expand += 1
    gap_upper = None
    gap_lower = None
    for row in rows:
        gap = abs(row["gap"])
        if gap == 0:
            continue
        if row["rho_sum"] > gap and gap_upper is None:
            gap_upper = {"n": row["n"], "word": row["word"], "rho_sum": row["rho_sum"], "gap": row["gap"]}
        if row["rho_sum"] < gap and gap_lower is None:
            gap_lower = {"n": row["n"], "word": row["word"], "rho_sum": row["rho_sum"], "gap": row["gap"]}
    return {
        "rho_gt_delta_on_expanding": fire_expand,
        "rho_gt_delta_anywhere": sum(1 for row in rows if row["rho_sum"] > row["delta"]),
        "n_expanding": len(expanding),
        "n_contracting": len(contracting),
        "rho_le_abs_gap_counterexample": gap_upper,
        "rho_ge_abs_gap_counterexample": gap_lower,
        "circular": (
            "Rho > surplus implies T<n only because Delta >= Rho and "
            "Delta > surplus iff T<n; it never fires on expanding rows"
        ),
    }


def telescope_search(n: int = 37, k: int = 6) -> dict[str, Any]:
    rec = walk(n, k)
    states = rec["states"]
    rhos = rec["rhos"]

    def eps_for(name: str, fn) -> list[int]:
        return [rhos[i] - (fn(states[i]) - fn(states[i + 1])) for i in range(len(rhos))]

    cands = {
        "id": eps_for("id", lambda x: x),
        "sq": eps_for("sq", lambda x: x * x),
        "cube": eps_for("cube", lambda x: x * x * x),
        "local_defect": eps_for("local_defect", local_defect),
    }
    known = path_pows_and_next_sq(states)
    return {
        "n": n,
        "word": rec["word"],
        "all_zero": {name: all(item == 0 for item in vals) for name, vals in cands.items()},
        "first_nonzero": {
            name: next((item for item in vals if item != 0), 0) for name, vals in cands.items()
        },
        "known_path_identity": known[0] == known[1] + rec["rho_sum"],
    }


def same_word_variation(word: str, *, n_max: int = 800) -> dict[str, Any]:
    rhos = []
    for n in range(1, n_max + 1):
        if follows_itinerary(n, word):
            rec = walk(n, len(word))
            if rec["word"] == word:
                rhos.append((n, rec["rho_sum"]))
    if not rhos:
        return {"word": word, "n_realizers": 0}
    lo, hi = min(rhos, key=lambda item: item[1]), max(rhos, key=lambda item: item[1])
    return {
        "word": word,
        "n_realizers": len(rhos),
        "min": {"n": lo[0], "rho_sum": lo[1]},
        "max": {"n": hi[0], "rho_sum": hi[1]},
        "varies": lo[1] != hi[1],
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + corpus
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "pathDefectSum": "def pathDefectSum" in text,
        "pathPows_eq_next_add_defects": "theorem pathPows_eq_next_add_defects" in text,
        "globalDefect": "def globalDefect" in combined,
        "no_new_rho": "def SumRho" not in combined and "def GlobalRho" not in combined,
        "no_ResidualState": "def ResidualState" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "FloorPower_absent": "pathDefectSum" not in floor,
    }


def run_probe() -> dict[str, Any]:
    hard = {n: walk(n, 8) for n in HARD_PROBES}
    identities = {str(n): identity_checks(walk(n, 6)) for n in (9, 10, 13, 37, 365)}
    rows = collect_rows()
    compact = [
        {
            "n": row["n"],
            "word": row["word"],
            "k": row["k"],
            "o": row["o"],
            "rho_sum": row["rho_sum"],
            "delta": row["delta"],
            "gap": row["gap"],
            "runs": row["runs"],
            "max_O": row["max_O"],
            "max_E": row["max_E"],
            "contracts": row["contracts"],
            "expands": row["expands"],
        }
        for row in rows
    ]
    return {
        "n_max": N_MAX,
        "k_max": K_MAX,
        "bit_limit": BIT_LIMIT,
        "n_rows": len(rows),
        "identities": identities,
        "h1": test_h1(rows),
        "h2": test_h2(rows),
        "h3": test_h3(rows),
        "h4": test_h4(rows),
        "telescope": telescope_search(),
        "same_word_ooe": same_word_variation("OOE"),
        "same_word_eoo": same_word_variation("EOO"),
        "hard": {
            str(n): {
                "word": rec["word"],
                "rho_sum": rec["rho_sum"],
                "delta": rec["delta"],
                "end": rec["end"],
                "overflow": rec["overflow"],
            }
            for n, rec in hard.items()
        },
        "rows_head": compact[:12],
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    if not lean["sorry_free"] or not lean["pathDefectSum"] or not lean["no_new_rho"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": f"lean_ok={lean}",
        }
    h1, h2, h3, h4 = scan["h1"], scan["h2"], scan["h3"], scan["h4"]
    tel = scan["telescope"]
    new_tel = any(tel["all_zero"].values())
    identities_ok = all(
        all(item.values()) for item in scan["identities"].values()
    )
    if new_tel and not tel["known_path_identity"]:
        return {
            "classification": CLASS_TELESCOPE,
            "secondary": [],
            "reason": "a new state potential telescopes Rho",
        }
    if h1["holds"]:
        return {
            "classification": CLASS_WORD,
            "secondary": ["H1"],
            "reason": "Rho is bounded by a function of (k,o) on this window",
        }
    if h3["holds"] and not h1["holds"]:
        return {
            "classification": CLASS_WORD,
            "secondary": ["H3"],
            "reason": "Rho is determined by (k,o,run signature) on this window",
        }
    if not h1["holds"] and not h3["holds"] and identities_ok:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": [CLASS_COUNTER, CLASS_REPACK],
            "reason": (
                "H1 and H3 fail: Rho varies at fixed (k,o) and at fixed "
                f"run signature (first H1 {h1['first']}; first H3 {h3['first']}); "
                f"H2 k*2n fails at {h2['k_times_2n']['first_counterexample']}; "
                f"H2 k*2n^3 fails at {h2['k_times_2n3']['first_counterexample']}; "
                "no new telescope (only pathPows = nextSquares + Rho); "
                f"H4 is the circular rewrite {h4['circular']}; "
                "same-word OOE Rho varies "
                f"({scan['same_word_ooe']})"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "secondary": [],
        "reason": f"no clean split h1={h1['holds']} h3={h3['holds']} id={identities_ok}",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["new_rho"] = False
    anti["residual_quotient_reopened"] = False
    anti["pe_factor_reopened"] = False
    anti["finite_residual_automaton"] = False
    anti["global_termination"] = False
    anti["new_scalar_energy"] = False
    anti["first_return_induction"] = False
    return {
        "experiment": "juggler_sum_rho",
        "algorithm_version": ALGORITHM_VERSION,
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "word prefixes n<=4000, k<=20, bit_limit=256; "
            "HARD_PROBES + PE 365/1999; fixed words OOE/OEO/EOO; "
            "H1-H4 on existing local_defect / pathDefectSum; no new rho"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    h1, h2, h3, h4 = scan["h1"], scan["h2"], scan["h3"], scan["h4"]
    lines = [
        "# Juggler global sum-rho / word-statistics",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Rho is the existing naive",
        "`pathDefectSum`, not a new remainder and not weighted Delta.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     does pathDefectSum admit a non-circular word-statistics bound?",
        "Novelty hypothesis      H1-H3, a new telescope, or a non-T<n H4",
        "Falsifier               H1-H3 fail; only known path identity; H4 is T<n",
        "Existing machinery      local_defect, pathDefectSum, globalDefect, powGap",
        "Maximum Phase-0 scope   n<=4000, k<=20, bit cap; H1-H4; no GPU/Lean/induction",
        "```",
        "",
        "## Metadata",
        "",
        f"- algorithm: `{payload['algorithm_version']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- rows: `{scan['n_rows']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- pathDefectSum present: `{lean['pathDefectSum']}`",
        "",
        decision["reason"] + ".",
        "",
        "Closed branches were not reopened: residual future-quotient,",
        "PE-factor grammar, R=Delta/S, scalar residual state.",
        "",
        "## Recovered identities",
        "",
    ]
    for n, row in scan["identities"].items():
        lines.append(f"- n=`{n}` `{row}`")
    lines.extend(
        [
            "",
            f"- telescope all-zero: `{scan['telescope']['all_zero']}`",
            f"- known path identity on the telescope probe: `{scan['telescope']['known_path_identity']}`",
            "",
            "## H1 pure word bound",
            "",
            f"- holds: `{h1['holds']}`",
            f"- groups: `{h1['n_groups']}` splits: `{h1['n_splits']}`",
            f"- first split: `{h1['first']}`",
            "",
            "## H2 scale-aware bound",
            "",
        ]
    )
    for name, row in h2.items():
        lines.append(
            f"- `{name}` holds=`{row['holds']}` "
            f"counterexample=`{row['first_counterexample']}` "
            f"worst=`{row['worst_ratio']}`"
        )
    lines.extend(
        [
            "",
            "## H3 run-sensitive bound",
            "",
            f"- holds: `{h3['holds']}`",
            f"- groups: `{h3['n_groups']}` splits: `{h3['n_splits']}`",
            f"- first split: `{h3['first']}`",
            "",
            "## H4 defect-compensated",
            "",
            f"- Rho > Delta anywhere: `{h4['rho_gt_delta_anywhere']}`",
            f"- Rho > Delta on expanding: `{h4['rho_gt_delta_on_expanding']}`",
            f"- Rho <= |gap| fails at: `{h4['rho_le_abs_gap_counterexample']}`",
            f"- Rho >= |gap| fails at: `{h4['rho_ge_abs_gap_counterexample']}`",
            f"- circularity: {h4['circular']}",
            "",
            "## Same-word variation",
            "",
            f"- OOE: `{scan['same_word_ooe']}`",
            f"- EOO: `{scan['same_word_eoo']}`",
            "",
            "## Hard traces",
            "",
        ]
    )
    for n, row in scan["hard"].items():
        lines.append(f"- n=`{n}` `{row}`")
    lines.extend(["", "## Lean", ""])
    for key, value in lean.items():
        lines.append(f"- {key}: `{value}`")
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
            "This is not a halt result. No new rho was defined.",
            "The PE-factor and residual-quotient branches were not reopened.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(json_safe(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    compact = {
        "decision": data["decision"],
        "n_rows": data["scan"]["n_rows"],
        "h1": data["scan"]["h1"],
        "h2": data["scan"]["h2"],
        "h3": data["scan"]["h3"],
        "h4": {
            "rho_gt_delta_anywhere": data["scan"]["h4"]["rho_gt_delta_anywhere"],
            "rho_gt_delta_on_expanding": data["scan"]["h4"]["rho_gt_delta_on_expanding"],
            "rho_le_abs_gap_counterexample": data["scan"]["h4"]["rho_le_abs_gap_counterexample"],
            "rho_ge_abs_gap_counterexample": data["scan"]["h4"]["rho_ge_abs_gap_counterexample"],
        },
        "telescope": data["scan"]["telescope"],
        "same_word_ooe": data["scan"]["same_word_ooe"],
        "hard": data["scan"]["hard"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(json_safe(compact), indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
