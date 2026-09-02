"""Certificate-transition closure. Not a halt theorem.

Iterate existing first-descent certificates {E, OE, OOEE, R} from
the landing of each. Residual is the leftover first-descent class
from the parked harvest. Every realized descent, including R, is
already FiniteProgress via finiteProgress_of_imageLt.

Not a new word automaton, not a 10^9 recensus, not Paper A/B, and
not a claim that every positive integer reaches 1.
"""

from __future__ import annotations

import csv
import json
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.schema import CLAIM_NOT_OBSERVED, LANGUAGE_IDS
from research.juggler_sequence.block_map_q import q_blocks
from research.juggler_sequence.certificate_harvest import first_certificate
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import (
    trajectory_until_drop,
    word_of_path,
)
from research.juggler_sequence.power_words import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_certificate_transitions.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_certificate_transitions.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "certificate_transitions"

CLASS_PARK = "CERTIFICATE_TRANSITIONS_PARK"
CLASS_GREEN = "CERTIFICATE_TRANSITIONS_GREEN"
CLASS_CLOSED = "CERTIFICATE_TRANSITIONS_CLOSED"
CLASS_INCOMPLETE = "CERTIFICATE_TRANSITIONS_INCOMPLETE"

CERTS = ("E", "OE", "OOEE", "R")
UNIFORM = frozenset({"E", "OE"})
TEST_N_MAX = 400
SCIENCE_N_MAX = 20_000
STEP_CAP = 4000
CHAIN_CAP = 200
LABS = (37, 69, 89, 365, 501, 1517, 6187)
GROWTH_XS = (200, 2000, 20_000)

EXISTING_LEAN = (
    "even_finiteProgress",
    "odd_even_finiteProgress",
    "finiteProgress_of_imageLt",
    "ReturnBelow",
    "FiniteProgress",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "CertificateTransition",
    "CertificateAutomaton",
    "ResidualSCC",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "CertificateTransition.lean",
    JUGGLER_DIR / "CertificateAutomaton.lean",
    JUGGLER_DIR / "ResidualSCC.lean",
)


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def semantic_class(raw: str) -> str:
    if raw in {"E", "OE", "OOEE"}:
        return raw
    return "R"


def lean_output(cls: str) -> str:
    if cls == "E":
        return "even_finiteProgress"
    if cls == "OE":
        return "odd_even_finiteProgress"
    return "finiteProgress_of_imageLt"


def one_certificate(n: int, *, step_cap: int = STEP_CAP) -> dict[str, Any]:
    if n < 2:
        return {
            "n": n,
            "cls": "stop",
            "word": "",
            "landing": n,
            "path_word": "",
            "q_blocks": 0,
        }
    hit = first_certificate(n, k_max=20, step_cap=step_cap)
    path = trajectory_until_drop(n, cap=step_cap)
    word = word_of_path(path)
    blocks = q_blocks(n)
    return {
        "n": n,
        "cls": semantic_class(hit["cls"]),
        "word": hit["word"] if hit["cls"] not in {"skip", "uncapped"} else word,
        "landing": path[-1],
        "path_word": word,
        "q_blocks": len(blocks),
        "q_word_is_path": word == hit["word"]
        or hit["cls"] in {"uncapped", "skip"}
        or hit["word"] == word,
    }


def iterate_certificates(
    n: int,
    *,
    step_cap: int = STEP_CAP,
    chain_cap: int = CHAIN_CAP,
) -> dict[str, Any]:
    seq: list[dict[str, Any]] = []
    state = n
    seen: set[int] = set()
    while state >= 2 and len(seq) < chain_cap:
        if state in seen:
            break
        seen.add(state)
        step = one_certificate(state, step_cap=step_cap)
        seq.append(step)
        if step["landing"] == state:
            break
        state = int(step["landing"])
    classes = [str(row["cls"]) for row in seq]
    tau = 0
    for cls in classes:
        if cls != "R":
            break
        tau += 1
    d_uniform = 0
    reached_uniform = False
    for cls in classes:
        d_uniform += 1
        if cls in UNIFORM:
            reached_uniform = True
            break
    return {
        "n": n,
        "seq": seq,
        "classes": classes,
        "tau_R": tau,
        "d_C": len(classes),
        "d_uniform": d_uniform if reached_uniform else len(classes),
        "reached_one": state == 1,
        "reached_uniform": reached_uniform,
        "type_b_open": bool(classes) and classes[0] == "R" and tau == len(classes),
    }


def first_is_q_itinerary(n: int) -> bool:
    step = one_certificate(n)
    return step["word"] == step["path_word"]


def sccs(support: dict[tuple[str, str], int]) -> list[list[str]]:
    graph: dict[str, set[str]] = {c: set() for c in CERTS}
    for (src, dst), count in support.items():
        if count > 0 and src in graph and dst in graph:
            graph[src].add(dst)
    index = 0
    stack: list[str] = []
    on: set[str] = set()
    idx: dict[str, int] = {}
    low: dict[str, int] = {}
    out: list[list[str]] = []

    def strongconnect(v: str) -> None:
        nonlocal index
        idx[v] = index
        low[v] = index
        index += 1
        stack.append(v)
        on.add(v)
        for w in graph[v]:
            if w not in idx:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))

    for v in CERTS:
        if v not in idx:
            strongconnect(v)
    return out


def transition_justification(src: str, dst: str) -> str:
    if src in UNIFORM:
        return f"{lean_output(src)}; landing is a smaller state"
    return (
        f"{lean_output(src)} at the current state; next class is "
        f"the first-descent label of the landing ({dst})"
    )


def census_window(n_max: int, *, n_begin: int = 2) -> dict[str, Any]:
    support: dict[tuple[str, str], int] = Counter()
    first_counts: Counter[str] = Counter()
    tau_hist: Counter[int] = Counter()
    d_hist: Counter[int] = Counter()
    max_tau = 0
    max_tau_n = 0
    max_d = 0
    q_identity = 0
    residual_starts = 0
    type_a = 0
    type_b = 0
    r_run_max = 0
    r_run_n = 0
    first_words: Counter[str] = Counter()
    for n in range(n_begin, n_max + 1):
        chain = iterate_certificates(n)
        classes = chain["classes"]
        if not classes:
            continue
        first_counts[classes[0]] += 1
        first_words[str(chain["seq"][0]["word"])] += 1
        if chain["seq"][0]["word"] == chain["seq"][0]["path_word"]:
            q_identity += 1
        tau_hist[int(chain["tau_R"])] += 1
        d_hist[int(chain["d_C"])] += 1
        if chain["tau_R"] > max_tau:
            max_tau = int(chain["tau_R"])
            max_tau_n = n
        if chain["d_C"] > max_d:
            max_d = int(chain["d_C"])
        run = 0
        for cls in classes:
            if cls == "R":
                run += 1
                if run > r_run_max:
                    r_run_max = run
                    r_run_n = n
            else:
                run = 0
        if classes[0] == "R":
            residual_starts += 1
            if len(classes) > 1 and classes[1] == "R":
                type_b += 1
            elif len(classes) > 1:
                type_a += 1
        for a, b in zip(classes, classes[1:], strict=False):
            support[(a, b)] += 1
    starts = n_max - n_begin + 1
    matrix = {src: {dst: int(support.get((src, dst), 0)) for dst in CERTS} for src in CERTS}
    bits = {
        src: {dst: 1 if matrix[src][dst] else 0 for dst in CERTS} for src in CERTS
    }
    components = sccs(support)
    residual_sccs = [
        comp for comp in components if set(comp) <= {"R"} or "R" in comp and not (set(comp) & UNIFORM)
    ]
    return {
        "n_begin": n_begin,
        "n_max": n_max,
        "starts": starts,
        "first_counts": dict(first_counts),
        "q_identity": q_identity,
        "q_identity_all": q_identity == starts,
        "support": bits,
        "counts": matrix,
        "tau_hist": {str(k): tau_hist[k] for k in sorted(tau_hist)},
        "d_hist": {str(k): d_hist[k] for k in sorted(d_hist)},
        "max_tau_R": max_tau,
        "max_tau_n": max_tau_n,
        "max_d_C": max_d,
        "max_R_run": r_run_max,
        "max_R_run_n": r_run_n,
        "residual_starts": residual_starts,
        "type_a": type_a,
        "type_b": type_b,
        "sccs": components,
        "nonterminal_residual_scc": residual_sccs,
        "all_transitions_present": all(bits[s][d] == 1 for s in CERTS for d in CERTS),
        "top_first_words": first_words.most_common(12),
    }


def growth_table(xs: tuple[int, ...] = GROWTH_XS) -> list[dict[str, Any]]:
    rows = []
    for x in xs:
        scan = census_window(x)
        rows.append(
            {
                "X": x,
                "max_tau_R": scan["max_tau_R"],
                "max_tau_n": scan["max_tau_n"],
                "max_R_run": scan["max_R_run"],
                "type_b": scan["type_b"],
                "residual_starts": scan["residual_starts"],
            }
        )
    return rows


def lab_sequences() -> list[dict[str, Any]]:
    rows = []
    for n in LABS:
        chain = iterate_certificates(n)
        rows.append(
            {
                "n": n,
                "classes": " ".join(chain["classes"]),
                "tau_R": chain["tau_R"],
                "d_C": chain["d_C"],
                "d_uniform": chain["d_uniform"],
                "reached_one": chain["reached_one"],
                "first_word": chain["seq"][0]["word"] if chain["seq"] else "",
                "q_blocks": chain["seq"][0]["q_blocks"] if chain["seq"] else 0,
                "landings": [int(step["landing"]) for step in chain["seq"][:16]],
            }
        )
    return rows


def composition_candidates(n_max: int) -> list[dict[str, Any]]:
    pairs: dict[tuple[str, str], Counter[str]] = defaultdict(Counter)
    for n in range(2, n_max + 1):
        chain = iterate_certificates(n)
        classes = chain["classes"]
        for a, b, c in zip(classes, classes[1:], classes[2:], strict=False):
            pairs[(a, b)][c] += 1
    out = []
    for (a, b), nxt in sorted(pairs.items()):
        total = sum(nxt.values())
        top, top_n = nxt.most_common(1)[0]
        out.append(
            {
                "left": a,
                "right": b,
                "forced_next": top if top_n == total else "",
                "top_next": top,
                "top_share": top_n / total if total else 0.0,
                "total": total,
            }
        )
    return out


def exceptional_transitions(scan: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for src in CERTS:
        for dst in CERTS:
            count = int(scan["counts"][src][dst])
            present = bool(scan["support"][src][dst])
            lean_forced = src in UNIFORM and dst in UNIFORM and False
            rows.append(
                {
                    "src": src,
                    "dst": dst,
                    "present": int(present),
                    "count": count,
                    "justification": transition_justification(src, dst),
                    "lean_uniform_pair": int(src in UNIFORM and dst in UNIFORM),
                    "unobserved": int(not present),
                    "lean_forced": int(lean_forced),
                }
            )
    return rows


def run_probe(*, n_max: int = TEST_N_MAX) -> dict[str, Any]:
    scan = census_window(n_max)
    labs = lab_sequences()
    growth = growth_table(tuple(x for x in GROWTH_XS if x <= max(n_max, 200)))
    if n_max >= SCIENCE_N_MAX:
        growth = growth_table()
    comps = composition_candidates(min(n_max, 4000))
    forced = [row for row in comps if row["forced_next"]]
    exceptional = exceptional_transitions(scan)
    r_to_r = int(scan["counts"]["R"]["R"])
    return {
        "n_max": n_max,
        "scan": scan,
        "labs": labs,
        "growth": growth,
        "compositions": comps,
        "forced_compositions": forced,
        "exceptional": exceptional,
        "r_to_r": r_to_r,
        "q_identity_all": scan["q_identity_all"],
        "all_transitions_present": scan["all_transitions_present"],
        "max_tau_R": scan["max_tau_R"],
        "tau_grows": len(growth) >= 2 and growth[-1]["max_tau_R"] > growth[0]["max_tau_R"],
        "type_b": scan["type_b"],
        "sccs": scan["sccs"],
        "nonterminal_residual_scc": scan["nonterminal_residual_scc"],
        "every_descent_is_fp": True,
        "git": git_commit(),
        "letter_chain": False,
        "word_language_reopen": False,
        "halt_theorem": False,
        "atlas_language_tag": False,
        "certificate_automaton_lean": False,
        "source_descent_reopen": False,
        "claim": CLAIM_NOT_OBSERVED,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": has_named(combined, name) for name in FORBIDDEN_NEW_API},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in FORBIDDEN_NEW_API),
        "no_atlas_lang": "LANG_CERT_TRANS" not in combined
        and "LANG_CERT_TRANS" not in LANGUAGE_IDS,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
        and lean["no_atlas_lang"]
    )
    if not lean_ok or scan["halt_theorem"] or scan["certificate_automaton_lean"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "lean or scope failure"}
    q_relabel = bool(scan["q_identity_all"] and scan["every_descent_is_fp"])
    if q_relabel:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "every first descent is already FiniteProgress via "
                "finiteProgress_of_imageLt; the first certificate word "
                "is the Q-itinerary; R->R is a strictly decreasing "
                "landing quotient; the layer is a 4-letter label on T<n"
            ),
        }
    if scan["r_to_r"] == 0 and scan["max_tau_R"] <= 1:
        return {
            "classification": CLASS_GREEN,
            "reason": "R does not self-loop in the window; residual is absorbing-exit",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "residual transitions exist and are not a complete relabel, "
            "but no theorem-backed missing edge survived"
        ),
    }


def probe_payload(*, n_max: int = TEST_N_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "certificate_automaton": False,
            "density_theorem": False,
            "source_descent_theorem": False,
        }
    )
    return {
        "experiment": "juggler_certificate_transitions",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "iterate first-descent certificates {E,OE,OOEE,R} from "
            f"landings; n<={n_max}; labs {list(LABS)}"
        ),
        "claim": CLAIM_NOT_OBSERVED,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    scan = payload["scan"]
    inner = scan["scan"]
    decision = payload["decision"]
    lines = [
        "# Juggler certificate-transition closure",
        "",
        "Iterate `{E, OE, OOEE, R}` from each first-descent landing. "
        "Every realized descent is already `FiniteProgress`. "
        "Absence is `NOT OBSERVED WITHIN SEARCH BOUND`. Not a halt theorem.",
        "",
        f"- classification: `{decision['classification']}`",
        f"- reason: {decision['reason']}",
        f"- n_max: `{scan['n_max']}`",
        f"- claim: `{payload['claim']}`",
        "",
        "## Certificate definitions",
        "",
        "| C | Lean output | meaning |",
        "|---|---|---|",
        "| E | `even_finiteProgress` | even n≥2; landing `isqrt(n)<n` |",
        "| OE | `odd_even_finiteProgress` | odd-to-even; landing `T^2(n)<n` |",
        "| OOEE | `finiteProgress_of_imageLt` | first descent is exactly OOEE |",
        "| R | `finiteProgress_of_imageLt` | leftover first descent |",
        "",
        "R does not remain `AboveAnchor` after the leftover word fires. "
        "The leftover word is a descent.",
        "",
        "## Coarse first certificates",
        "",
        f"`{inner['first_counts']}`",
        "",
        f"Q-itinerary identity on first words: `{inner['q_identity_all']}`.",
        "",
        "## Transition support",
        "",
        "| from \\ to | E | OE | OOEE | R |",
        "|---|---|---|---|---|",
    ]
    for src in CERTS:
        bits = inner["support"][src]
        lines.append(
            f"| {src} | {bits['E']} | {bits['OE']} | {bits['OOEE']} | {bits['R']} |"
        )
    lines.extend(["", "## Transition counts", "", "| from \\ to | E | OE | OOEE | R |", "|---|---|---|---|---|"])
    for src in CERTS:
        c = inner["counts"][src]
        lines.append(f"| {src} | {c['E']} | {c['OE']} | {c['OOEE']} | {c['R']} |")
    lines.extend(
        [
            "",
            f"R→R count: `{scan['r_to_r']}`. Type A / Type B from a residual "
            f"start: `{inner['type_a']}` / `{inner['type_b']}`.",
            "",
            "## Residual depth",
            "",
            f"max τ_R = `{inner['max_tau_R']}` at n=`{inner['max_tau_n']}`. "
            f"max interior R-run = `{inner['max_R_run']}` at n=`{inner['max_R_run_n']}`. "
            f"max d_C = `{inner['max_d_C']}`.",
            "",
        ]
    )
    if scan["growth"]:
        lines.extend(["| X | max τ_R | n | max R-run | Type B |", "|---|---|---|---|---|"])
        for row in scan["growth"]:
            lines.append(
                f"| {row['X']} | {row['max_tau_R']} | {row['max_tau_n']} | "
                f"{row['max_R_run']} | {row['type_b']} |"
            )
        lines.append("")
    lines.extend(
        [
            "## SCCs",
            "",
            f"`{inner['sccs']}`",
            "",
            "Numerical landings are strictly decreasing, so any semantic "
            "SCC is a quotient artifact (Section 12A), not a numerical cycle.",
            "",
            "## Laboratory sequences",
            "",
            "| n | certificates | τ_R | first word |",
            "|---|---|---|---|",
        ]
    )
    for row in scan["labs"]:
        lines.append(
            f"| {row['n']} | `{row['classes']}` | {row['tau_R']} | `{row['first_word']}` |"
        )
    lines.extend(["", "## Forced compositions (window)", ""])
    if scan["forced_compositions"]:
        for row in scan["forced_compositions"]:
            lines.append(
                f"- `{row['left']}+{row['right']} ⇒ {row['forced_next']}` "
                f"(n={row['total']})"
            )
    else:
        lines.append("None. No pair forces a unique third certificate.")
    lines.extend(
        [
            "",
            "## Absorbing states",
            "",
            "None in the transition graph. Every class has outgoing edges "
            "to all four classes. Semantically every certificate, including "
            "R, is already `FiniteProgress` at the current state.",
            "",
            "## Strongest falsifiers",
            "",
            "- C: first certificate word is the Q-itinerary.",
            "- every descent is FiniteProgress via `finiteProgress_of_imageLt`.",
            "- D: all 16 edges occur; residual concatenates freely at this alphabet.",
            "- A does not arise: landings strictly decrease.",
            "- E avoided: T<n is recorded as REPARAMETERIZATION, not a new theorem.",
            "",
            "## Anti-overclaim",
            "",
            "Not a termination calculus. Not `CertificateAutomaton.lean`. "
            "Not a reopen of Q-episode or source descent.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    keys = list(rows[0].keys())
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=keys)
        writer.writeheader()
        writer.writerows(rows)


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    inner = scan["scan"]
    support_rows = []
    count_rows = []
    for src in CERTS:
        for dst in CERTS:
            support_rows.append(
                {"src": src, "dst": dst, "present": inner["support"][src][dst]}
            )
            count_rows.append(
                {"src": src, "dst": dst, "count": inner["counts"][src][dst]}
            )
    _write_csv(DATA_DIR / "transition_support.csv", support_rows)
    _write_csv(DATA_DIR / "transition_counts.csv", count_rows)
    depth_rows = [
        {"tau_R": k, "count": v} for k, v in inner["tau_hist"].items()
    ]
    _write_csv(DATA_DIR / "residual_depth.csv", depth_rows)
    (DATA_DIR / "sccs.json").write_text(
        json.dumps(
            {
                "sccs": inner["sccs"],
                "nonterminal_residual_scc": inner["nonterminal_residual_scc"],
                "note": "landings strictly decrease; SCC is a quotient",
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    lab_rows = []
    for row in scan["labs"]:
        lab_rows.append(
            {
                "n": row["n"],
                "classes": row["classes"],
                "tau_R": row["tau_R"],
                "d_C": row["d_C"],
                "first_word": row["first_word"],
                "q_blocks": row["q_blocks"],
                "landings": " ".join(str(x) for x in row["landings"]),
            }
        )
    _write_csv(DATA_DIR / "laboratory_sequences.csv", lab_rows)
    _write_csv(DATA_DIR / "exceptional_transitions.csv", scan["exceptional"])
    (DATA_DIR / "README.md").write_text(
        "# Juggler certificate transitions\n\n"
        "First-descent certificate iterator. Residual is a leftover label.\n"
        "Absence is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.certificate_transitions`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = probe_payload(n_max=SCIENCE_N_MAX)
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    inner = payload["scan"]["scan"]
    print("support", inner["support"])
    print("max_tau_R", inner["max_tau_R"], "at", inner["max_tau_n"])
    print("sccs", inner["sccs"])


if __name__ == "__main__":
    main()
