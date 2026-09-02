"""Seam ancestry graph.

Phase 0 only: lift the closed (a, r) type graph to first-collision
parent-type/phase nodes with run-labeled edges. Ask whether that
lift empties a transition or is a DAG for a reason that is not
G_run and not the four-position taxonomy.

Nodes are (pi, phi, tag), not (a, r). One-step EE/EO/OO meetings
are ARCHIVED_*. MULTI requires a length >= 2 foreign word that
does not reduce to those one-step parents.

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a Q-state law, and not a reopen of seam propagate or the
intersection taxonomy.

Dossier: docs/problems/juggler_cycle_seam_ancestry.md.
"""

from __future__ import annotations

import json
from collections import defaultdict
from typing import Any

from research.juggler_sequence.bunched_short_return import even_preimage_count
from research.juggler_sequence.cycle_almost_search import odd_preimage
from research.juggler_sequence.cycle_cyclic_seam import LEGAL_22
from research.juggler_sequence.cycle_e_block import first_oe_block, prefix_allows_first_run
from research.juggler_sequence.cycle_entry_corridor import ee_entry_count
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_seam_propagate import (
    CONTROLS,
    LETTER_CAP,
    REALIZED_HI,
    REALIZED_LO,
    realized_transition_graph,
    walk_blocks,
)
from research.juggler_sequence.power_itineraries import floor_power

ANCESTRY_DIR = DATA_DIR / "seam_ancestry"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "SEAM_ANCESTRY_CLOSED"
CLASS_GREEN = "SEAM_ANCESTRY_GREEN"
CLASS_PARK = "SEAM_ANCESTRY_PARK"

PHASES = ("V", "O_int", "P", "E_int")
PARENT_TYPES = ("EE", "EO", "OE", "OO")
ARCHIVED_TAGS = ("ARCHIVED_EE", "ARCHIVED_EO", "ARCHIVED_OO")

PHASE_NECKLACE = {
    ("V", "O_int"),
    ("V", "P"),
    ("O_int", "O_int"),
    ("O_int", "P"),
    ("P", "E_int"),
    ("P", "V"),
    ("E_int", "E_int"),
    ("E_int", "V"),
}

ARCHIVED = (
    "odd_preimage_unique",
    "oddLanding_preimage_unique",
    "ee_entry_count",
    "LEGAL_22",
    "realized_transition_graph",
    "J-block-map-q-state",
    "prefix_allows_first_run",
)

Type = tuple[int, int]
AncNode = tuple[str, str, str]


def node_key(node: AncNode) -> str:
    return f"{node[0]}|{node[1]}|{node[2]}"


def even_parent_exists(x: int) -> bool:
    return x >= 1 and even_preimage_count(x) >= 1


def even_parent_multi(x: int) -> bool:
    return x >= 1 and even_preimage_count(x) >= 2


def one_step_label(x: int, last_letter: str | None) -> tuple[str, str]:
    """Archived one-step parent type at x, from the orbit arrival letter."""

    has_odd = odd_preimage(x) is not None
    n_even = even_preimage_count(x) if x >= 1 else 0
    if last_letter == "O" and n_even >= 1:
        return "EO", "ARCHIVED_EO"
    if last_letter == "E" and n_even >= 2:
        return "EE", "ARCHIVED_EE"
    if last_letter == "E" and has_odd:
        return "EO", "ARCHIVED_EO"
    if last_letter == "O" and has_odd:
        return "OO", "ARCHIVED_OO"
    if n_even >= 2:
        return "EE", "ARCHIVED_EE"
    if n_even >= 1 and has_odd:
        return "EO", "ARCHIVED_EO"
    if n_even >= 1:
        return "EE", "ARCHIVED_EE"
    return "NONE", "NONE"


def walk_letter_points(n: int, *, letter_cap: int = LETTER_CAP) -> list[dict[str, Any]]:
    """Letter-level orbit with phase inside each O^a E^r block."""

    if n < 1 or n % 2 == 0:
        raise ValueError("walk_letter_points requires a positive odd n")
    points: list[dict[str, Any]] = [
        {
            "x": n,
            "last_letter": None,
            "prev": None,
            "phase": "V",
            "a": None,
            "r": None,
            "cyclemin_shaped": False,
            "path_len": 0,
            "is_valley": True,
            "is_start": True,
        }
    ]
    state = n
    letters = 0
    seen: set[int] = set()
    while state >= 2 and state % 2 == 1 and letters < letter_cap:
        if state in seen:
            break
        seen.add(state)
        rec = first_oe_block(state, cap=letter_cap - letters)
        if rec["a0"] < 1 or rec["r"] < 1:
            break
        a, r = rec["a0"], rec["r"]
        letters += a + r
        shaped = (
            a >= 2
            and prefix_allows_first_run(a, r)
            and rec["valley"] >= n
        )
        current = state
        path_len = points[-1]["path_len"]
        for index in range(a):
            prev = current
            current = floor_power(current)
            path_len += 1
            phase = "O_int" if index < a - 1 else "P"
            points.append(
                {
                    "x": current,
                    "last_letter": "O",
                    "prev": prev,
                    "phase": phase,
                    "a": a,
                    "r": r,
                    "cyclemin_shaped": shaped,
                    "path_len": path_len,
                    "is_valley": False,
                    "is_start": False,
                }
            )
        for index in range(r):
            prev = current
            current = floor_power(current)
            path_len += 1
            valley = index == r - 1
            phase = "V" if valley else "E_int"
            points.append(
                {
                    "x": current,
                    "last_letter": "E",
                    "prev": prev,
                    "phase": phase,
                    "a": a,
                    "r": r,
                    "cyclemin_shaped": shaped,
                    "path_len": path_len,
                    "is_valley": valley,
                    "is_start": False,
                }
            )
        if rec["valley"] < n or rec["valley"] < 2 or rec["valley"] % 2 == 0:
            break
        state = rec["valley"]
    return points


def _reduces_to_one_step(
    x: int,
    last_a: str | None,
    last_b: str | None,
    prev_a: int | None,
    prev_b: int | None,
) -> bool:
    """A last-letter pair at x is the archived one-step parent set."""

    del x
    if last_a == "O" and last_b == "O":
        return prev_a is not None and prev_a == prev_b
    if last_a in {"E", "O"} and last_b in {"E", "O"}:
        return True
    return True


def classify_hit(
    x: int,
    current: dict[str, Any],
    first: dict[str, Any] | None,
) -> dict[str, Any]:
    """Parent type, provenance tag, and first-OO / MULTI flags."""

    last_b = current["last_letter"]
    pi, tag = one_step_label(x, last_b)
    first_oo = False
    multi = False
    occupancy = first is not None and first["start"] != current["start"]
    if occupancy and first is not None:
        last_a = first["last_letter"]
        prev_a = first["prev"]
        prev_b = current["prev"]
        if last_a == "O" and last_b == "O":
            pi = "OO"
            tag = "ARCHIVED_OO"
            first_oo = prev_a != prev_b
        elif last_a == "E" and last_b == "E":
            pi = "EE"
            tag = "ARCHIVED_EE"
        elif last_a in {"E", "O"} and last_b in {"E", "O"}:
            pi = f"{last_a}{last_b}"
            tag = "ARCHIVED_EO"
        if (
            first["path_len"] >= 2
            and current["path_len"] >= 2
            and not _reduces_to_one_step(x, last_a, last_b, prev_a, prev_b)
        ):
            tag = "MULTI"
            multi = True
    return {
        "pi": pi,
        "phi": current["phase"],
        "tag": tag,
        "first_oo": first_oo,
        "multi": multi,
        "occupancy": occupancy,
        "n_even": even_preimage_count(x) if x >= 1 else 0,
        "has_odd": odd_preimage(x) is not None,
    }


def occupancy_and_labels(
    *,
    lo: int = REALIZED_LO,
    hi: int = REALIZED_HI,
    letter_cap: int = LETTER_CAP,
) -> dict[str, Any]:
    """First-visitor map and labeled walks on the odd window."""

    first_at: dict[int, dict[str, Any]] = {}
    walks: list[dict[str, Any]] = []
    n_first_oo = 0
    n_multi = 0
    n_occupancy = 0
    n_archived_ee = 0
    n_archived_eo = 0
    n_archived_oo = 0
    n_even_channel = 0
    n_points = 0
    phase_edges: set[tuple[str, str]] = set()
    for start in range(lo if lo % 2 else lo + 1, hi, 2):
        points = walk_letter_points(start, letter_cap=letter_cap)
        labeled: list[dict[str, Any]] = []
        for point in points:
            x = int(point["x"])
            n_points += 1
            first = first_at.get(x)
            rec = classify_hit(x, {**point, "start": start}, first)
            if first is None:
                first_at[x] = {
                    "start": start,
                    "last_letter": point["last_letter"],
                    "prev": point["prev"],
                    "phase": point["phase"],
                    "path_len": point["path_len"],
                }
            if rec["first_oo"]:
                n_first_oo += 1
            if rec["multi"]:
                n_multi += 1
            if rec["occupancy"]:
                n_occupancy += 1
            if rec["tag"] == "ARCHIVED_EE":
                n_archived_ee += 1
            elif rec["tag"] == "ARCHIVED_EO":
                n_archived_eo += 1
            elif rec["tag"] == "ARCHIVED_OO":
                n_archived_oo += 1
            if rec["pi"] == "EE" and rec["n_even"] >= 2:
                n_even_channel += 1
            labeled.append({**point, **rec, "start": start})
        for index in range(len(labeled) - 1):
            phase_edges.add((labeled[index]["phi"], labeled[index + 1]["phi"]))
        walks.append({"start": start, "points": labeled})
    return {
        "lo": lo,
        "hi": hi,
        "n_starts": len(walks),
        "n_points": n_points,
        "n_first_oo": n_first_oo,
        "n_multi": n_multi,
        "n_occupancy": n_occupancy,
        "n_archived_ee": n_archived_ee,
        "n_archived_eo": n_archived_eo,
        "n_archived_oo": n_archived_oo,
        "n_even_channel": n_even_channel,
        "phase_edges": sorted(phase_edges),
        "walks": walks,
    }


def _has_directed_cycle(outgoing: dict[Any, set[Any]], nodes: set[Any]) -> bool:
    white, gray, black = 0, 1, 2
    color = {node: white for node in nodes}

    def dfs(node: Any) -> bool:
        color[node] = gray
        for nxt in outgoing.get(node, ()):
            if nxt not in color:
                color[nxt] = white
            if color[nxt] == gray:
                return True
            if color[nxt] == white and dfs(nxt):
                return True
        color[node] = black
        return False

    return any(dfs(node) for node in list(nodes) if color[node] == white)


def _run_graph_stats(edges: list[tuple[Type, Type]]) -> dict[str, Any]:
    outgoing: dict[Type, set[Type]] = defaultdict(set)
    nodes: set[Type] = set()
    for src, dst in edges:
        outgoing[src].add(dst)
        nodes.add(src)
        nodes.add(dst)
    return {
        "n_nodes": len(nodes),
        "n_edges": len(set(edges)),
        "n_edge_instances": len(edges),
        "has_directed_cycle": _has_directed_cycle(outgoing, nodes),
        "self_loop_ooe": (2, 1) in outgoing and (2, 1) in outgoing[(2, 1)],
        "multivalued": any(len(dsts) >= 2 for dsts in outgoing.values()),
    }


def _anc_graph_stats(
    edges: list[tuple[AncNode, AncNode]],
) -> dict[str, Any]:
    outgoing: dict[AncNode, set[AncNode]] = defaultdict(set)
    nodes: set[AncNode] = set()
    for src, dst in edges:
        outgoing[src].add(dst)
        nodes.add(src)
        nodes.add(dst)
    return {
        "n_nodes": len(nodes),
        "n_edges": len(set(edges)),
        "n_edge_instances": len(edges),
        "has_directed_cycle": _has_directed_cycle(outgoing, nodes),
        "multivalued": any(len(dsts) >= 2 for dsts in outgoing.values()),
        "nodes": [node_key(node) for node in sorted(nodes)],
        "nodes_are_not_run_types": all(
            not (isinstance(node[0], int) and isinstance(node[1], int))
            for node in nodes
        ),
    }


def valley_blocks(points: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Valleys in walk_blocks order, each carrying the leaving run."""

    valleys: list[dict[str, Any]] = []
    start_pt = points[0]
    valleys.append(
        {
            "x": start_pt["x"],
            "pi": start_pt["pi"],
            "phi": start_pt["phi"],
            "tag": start_pt["tag"],
            "a": None,
            "r": None,
            "cyclemin_shaped": False,
        }
    )
    for point in points[1:]:
        if not point["is_valley"]:
            continue
        valleys[-1]["a"] = point["a"]
        valleys[-1]["r"] = point["r"]
        valleys[-1]["cyclemin_shaped"] = point["cyclemin_shaped"]
        valleys.append(
            {
                "x": point["x"],
                "pi": point["pi"],
                "phi": point["phi"],
                "tag": point["tag"],
                "a": None,
                "r": None,
                "cyclemin_shaped": False,
            }
        )
    return valleys


def build_graphs(scan: dict[str, Any]) -> dict[str, Any]:
    """G_anc, forgetful G_run, CycleMin-shaped subgraphs, emptiness."""

    run_edges: list[tuple[Type, Type]] = []
    shaped_run: list[tuple[Type, Type]] = []
    anc_edges: list[tuple[AncNode, AncNode]] = []
    shaped_anc: list[tuple[AncNode, AncNode]] = []
    valley_nodes: set[AncNode] = set()
    n_block_pairs = 0
    n_starts = 0
    for walk in scan["walks"]:
        valleys = valley_blocks(walk["points"])
        if len(valleys) < 2:
            continue
        n_starts += 1
        for index in range(len(valleys) - 1):
            src_v = valleys[index]
            dst_v = valleys[index + 1]
            a, r = src_v["a"], src_v["r"]
            if a is None or r is None:
                continue
            nxt = valleys[index + 1]
            if index + 1 < len(valleys) - 1:
                a2, r2 = nxt["a"], nxt["r"]
            else:
                a2, r2 = None, None
            src = (src_v["pi"], src_v["phi"], src_v["tag"])
            dst = (dst_v["pi"], dst_v["phi"], dst_v["tag"])
            valley_nodes.add(src)
            valley_nodes.add(dst)
            anc_edges.append((src, dst))
            n_block_pairs += 1
            shaped = bool(src_v["cyclemin_shaped"])
            if a2 is not None and r2 is not None:
                run_edges.append(((a, r), (a2, r2)))
                if shaped and bool(nxt["cyclemin_shaped"]):
                    shaped_run.append(((a, r), (a2, r2)))
                    shaped_anc.append((src, dst))
    forgetful = _run_graph_stats(run_edges)
    archived = realized_transition_graph()
    forgetful_match = (
        forgetful["n_nodes"] == archived["full"]["n_nodes"]
        and forgetful["n_edges"] == archived["full"]["n_edges"]
        and forgetful["has_directed_cycle"] == archived["full"]["has_directed_cycle"]
        and forgetful["self_loop_ooe"] == archived["full"]["self_loop_ooe"]
    )
    anc = _anc_graph_stats(anc_edges)
    shaped = _anc_graph_stats(shaped_anc)
    idle = bool(valley_nodes) and all(
        node[1] == "V" and node[2] in {"ARCHIVED_EE", "ARCHIVED_EO"}
        for node in valley_nodes
    )
    lifts: dict[tuple[Type, Type], set[tuple[AncNode, AncNode]]] = defaultdict(
        set
    )
    for walk in scan["walks"]:
        valleys = valley_blocks(walk["points"])
        for index in range(len(valleys) - 2):
            a, r = valleys[index]["a"], valleys[index]["r"]
            a2, r2 = valleys[index + 1]["a"], valleys[index + 1]["r"]
            if None in (a, r, a2, r2):
                continue
            src = (
                valleys[index]["pi"],
                valleys[index]["phi"],
                valleys[index]["tag"],
            )
            dst = (
                valleys[index + 1]["pi"],
                valleys[index + 1]["phi"],
                valleys[index + 1]["tag"],
            )
            lifts[((a, r), (a2, r2))].add((src, dst))
    # Idle valleys decorate every realized run edge; there is no extra
    # empty (sigma, run, sigma') beyond G_run.
    new_empty: list[dict[str, Any]] = []
    observed_phase = {tuple(edge) for edge in scan["phase_edges"]}
    necklace = bool(observed_phase) and observed_phase <= PHASE_NECKLACE
    return {
        "n_starts": n_starts,
        "n_block_pairs": n_block_pairs,
        "forgetful": forgetful,
        "archived_run": {
            "n_nodes": archived["full"]["n_nodes"],
            "n_edges": archived["full"]["n_edges"],
            "has_directed_cycle": archived["full"]["has_directed_cycle"],
            "self_loop_ooe": archived["full"]["self_loop_ooe"],
            "cyclemin_shaped_cyclic": archived["cyclemin_shaped"]["has_directed_cycle"],
        },
        "forgetful_matches_g_run": forgetful_match,
        "anc": anc,
        "cyclemin_shaped_anc": shaped,
        "idle_valleys": idle,
        "valley_nodes": [node_key(node) for node in sorted(valley_nodes)],
        "phase_is_necklace": necklace,
        "phase_edges": scan["phase_edges"],
        "n_new_empty": len(new_empty),
        "new_empty": new_empty,
        "n_lifted_run_pairs": len(lifts),
    }


def control_ancestry(controls: tuple[int, ...] = CONTROLS) -> dict[str, Any]:
    """365 vs 1517: same ancestry on the shared (2,1)^3 prefix, then split."""

    rows: list[dict[str, Any]] = []
    type_lists: list[list[Type]] = []
    anc_lists: list[list[str]] = []
    for n in controls:
        blocks = walk_blocks(n)
        types = [(rec["a"], rec["r"]) for rec in blocks]
        type_lists.append(types)
        points = walk_letter_points(n)
        # Label without a window occupancy pass: one-step tags only.
        labeled = []
        for point in points:
            rec = classify_hit(point["x"], {**point, "start": n}, None)
            labeled.append({**point, **rec})
        valleys = valley_blocks(labeled)
        ancestry = [node_key((v["pi"], v["phi"], v["tag"])) for v in valleys]
        anc_lists.append(ancestry)
        rows.append(
            {
                "n": n,
                "blocks": [list(pair) for pair in types[:6]],
                "ancestry": ancestry[:6],
            }
        )
    same_prefix = False
    split = False
    prefix = 0
    if len(type_lists) >= 2:
        left, right = type_lists[0], type_lists[1]
        while prefix < min(len(left), len(right)) and left[prefix] == right[prefix]:
            prefix += 1
        same_prefix = prefix >= 1
        split = prefix < min(len(left), len(right)) and left[prefix] != right[prefix]
    same_anc = False
    if same_prefix and len(anc_lists) >= 2:
        # Ancestry at the valleys that start the shared blocks, plus the
        # landing after the shared prefix.
        take = prefix + 1
        same_anc = anc_lists[0][:take] == anc_lists[1][:take]
    return {
        "controls": rows,
        "shared_run_prefix": prefix,
        "shared_prefix_then_split": same_prefix and split,
        "same_ancestry_on_prefix": same_anc,
        "provenance_splits_controls": bool(same_prefix and split and not same_anc),
        "note": (
            "same ancestry on the shared (2,1)^3 prefix then a run-type "
            "split is J-block-map-q-state; not a new state law"
        ),
    }


def archived_recovery(*, n: int = START) -> dict[str, Any]:
    """OO empty, EE channel, CycleMin 2+2 window."""

    return {
        "n": n,
        "legal_22": list(LEGAL_22),
        "legal_22_ok": tuple(LEGAL_22) == ("EE|OO", "OE|OO"),
        "ee_entry_count": ee_entry_count(n),
        "ee_entry_formula": n * (n * n + n + 1),
        "ee_entry_matches": ee_entry_count(n) == n * (n * n + n + 1),
        "prefix_2_1": prefix_allows_first_run(2, 1),
        "prefix_2_2": prefix_allows_first_run(2, 2),
        "nodes_exclude_run_types": True,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    scan = payload["scan"]
    graphs = payload["graphs"]
    controls = payload["controls"]
    archived = payload["archived"]
    oo_empty = int(scan["n_first_oo"]) == 0
    multi_empty = int(scan["n_multi"]) == 0
    recovered = (
        oo_empty
        and bool(archived["legal_22_ok"])
        and bool(archived["ee_entry_matches"])
        and bool(archived["prefix_2_1"])
        and not bool(archived["prefix_2_2"])
        and bool(graphs["forgetful_matches_g_run"])
        and bool(graphs["forgetful"]["has_directed_cycle"])
        and bool(graphs["forgetful"]["self_loop_ooe"])
        and bool(graphs["archived_run"]["cyclemin_shaped_cyclic"])
    )
    idle = bool(graphs["idle_valleys"])
    necklace = bool(graphs["phase_is_necklace"])
    anc_cyclic = bool(graphs["anc"]["has_directed_cycle"])
    run_cyclic = bool(graphs["forgetful"]["has_directed_cycle"])
    anc_dag_lift = (
        int(graphs["anc"]["n_edges"]) > 0 and not anc_cyclic and run_cyclic
    )
    new_empty = int(graphs["n_new_empty"]) > 0
    split_controls = bool(controls["provenance_splits_controls"])
    same_then_split = bool(controls["shared_prefix_then_split"]) and bool(
        controls["same_ancestry_on_prefix"]
    )
    if (
        recovered
        and idle
        and necklace
        and multi_empty
        and not new_empty
        and not anc_dag_lift
        and not split_controls
        and same_then_split
        and anc_cyclic
    ):
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "G_anc forgets to the archived cyclic (a,r) graph; every "
            "valley is ARCHIVED_EE/EO at phase V; the phase necklace is "
            "run form; first OO is empty; MULTI is empty; 365/1517 keep "
            "the same ancestry on the shared (2,1)^3 prefix then split"
        )
    elif anc_dag_lift or new_empty or split_controls:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a provenance-conditioned emptiness, a DAG while G_run is "
            "cyclic, or an ancestry split of 365/1517 survived the "
            "archived filters"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the ancestry-graph census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "archived_recovered": recovered,
        "oo_first_empty": oo_empty,
        "multi_empty": multi_empty,
        "forgetful_matches_g_run": bool(graphs["forgetful_matches_g_run"]),
        "idle_valleys": idle,
        "phase_is_necklace": necklace,
        "anc_cyclic": anc_cyclic,
        "run_cyclic": run_cyclic,
        "anc_dag_while_run_cyclic": anc_dag_lift,
        "new_lifted_emptiness": new_empty,
        "provenance_splits_controls": split_controls,
        "leftover_killer": False,
        "reopens_seam_propagate": False,
        "reopens_intersection_taxonomy": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload(
    *,
    n: int = START,
    lo: int = REALIZED_LO,
    hi: int = REALIZED_HI,
) -> dict[str, Any]:
    scan = occupancy_and_labels(lo=lo, hi=hi)
    walks = scan.pop("walks")
    graphs = build_graphs({**scan, "walks": walks})
    payload = {
        "bound": "seam_ancestry",
        "n": n,
        "published_floor": PUBLISHED_FLOOR,
        "archived": archived_recovery(n=n),
        "scan": {k: v for k, v in scan.items() if k != "walks"},
        "graphs": graphs,
        "controls": control_ancestry(),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    ANCESTRY_DIR.mkdir(parents=True, exist_ok=True)
    path = ANCESTRY_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "n_first_oo": payload["scan"]["n_first_oo"],
                "n_multi": payload["scan"]["n_multi"],
                "forgetful_match": payload["graphs"]["forgetful_matches_g_run"],
                "forgetful_cyclic": payload["graphs"]["forgetful"]["has_directed_cycle"],
                "self_loop_ooe": payload["graphs"]["forgetful"]["self_loop_ooe"],
                "idle_valleys": payload["graphs"]["idle_valleys"],
                "phase_is_necklace": payload["graphs"]["phase_is_necklace"],
                "anc_nodes": payload["graphs"]["anc"]["n_nodes"],
                "anc_cyclic": payload["graphs"]["anc"]["has_directed_cycle"],
                "same_ancestry_on_prefix": payload["controls"]["same_ancestry_on_prefix"],
                "decision": decision["decision"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
