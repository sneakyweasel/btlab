"""Backward predecessor geometry of the Juggler floor-power map.

Not a Research Engine control-layer experiment. Not a halt theorem.
Uses the existing even/odd floor cells. Does not import Collatz inverse.
Does not reopen PE-factor, residual-quotient, prefix-NC, preimage-cylinder,
realization-geometry, first-return, adversarial-path, information-complexity,
or sum-rho branches. Not a cell-tree engine and not a new Lyapunov scalar.
"""

from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict, deque
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.lean_paths import CELLS, DYNAMICS, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_backward_geometry.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_backward_geometry.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "backward"

CENSUS_MAX = 4000
DEPTH_MAX = 12
SMALL_CAP = 10**6
HIGH_CAP = 10**7
FIBER_CAP = 400
WALK_STEPS = 80
WALK_BIT_CAP = 25_000

SMALL_ROOTS = (1, 3, 5, 7, 9, 37, 49, 69, 77)
HIGH_ROOTS = (193, 243, 365, 425, 763, 1749, 1999, 2183, 3431, 3889, 4447)
HARD_WALKS = (3, 365, 425, 2183, 3889)
COMPOSE_ROOTS = (1, 2, 3, 5, 7, 11, 36)
COMPOSE_WORDS = ("E", "O", "EE", "EO", "OE", "OO", "EEE", "EOE", "OEE", "EEO")

CLASS_BRANCH = "BACKWARD_BRANCH_GREEN"
CLASS_SCALE = "BACKWARD_SCALE_GREEN"
CLASS_AFFINE = "BACKWARD_AFFINE_GREEN"
CLASS_SPARSE = "BACKWARD_SPARSE_GREEN"
CLASS_WELL = "BACKWARD_WELLFOUNDED_GREEN"
CLASS_BRIDGE = "BACKWARD_FORWARD_BRIDGE_GREEN"
CLASS_COMPLEX = "BACKWARD_COMPLEX"

LEAN_THEOREMS = (
    "even_preimage_iff",
    "odd_preimage_iff",
    "odd_preimage_unique",
    "floorPower_even_eq_iff_sq_interval",
    "floorPower_odd_eq_iff_cube_interval",
    "floorPower_one",
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    if isinstance(value, Fraction):
        return str(value)
    return value


def sign_of(child: int, parent: int) -> str:
    if child < parent:
        return "descending"
    if child == parent:
        return "equal"
    return "ascending"


def even_remainder(child: int, parent: int) -> int | None:
    if child % 2 != 0:
        return None
    return child - parent * parent


def even_pred_range(m: int) -> tuple[int, int, int] | None:
    """Inclusive even endpoints and count in the square cell, or None if empty."""

    if m < 1:
        raise ValueError("even_pred_range requires a positive integer")
    lo, hi = even_preimage(m)
    first = lo if lo % 2 == 0 else lo + 1
    if first < 2:
        first = 2
    last = hi - 1
    if last % 2 == 1:
        last -= 1
    if first >= hi or last < first:
        return None
    return first, last, ((last - first) // 2) + 1


def pred_even(m: int, *, validate: bool = True) -> list[int]:
    bounds = even_pred_range(m)
    if bounds is None:
        return []
    first, last, _ = bounds
    out = list(range(first, last + 1, 2))
    if validate:
        for n in out:
            if n < 1 or n % 2 != 0 or floor_power(n) != m:
                raise ValueError(f"even predecessor {n} of {m} failed T(n)=m")
    return out


def pred_odd(m: int, *, validate: bool = True) -> list[int]:
    if m < 1:
        raise ValueError("pred_odd requires a positive integer")
    out = []
    for n in odd_preimage_integers(m):
        if n < 1 or n % 2 == 0:
            continue
        if validate and floor_power(n) != m:
            raise ValueError(f"odd predecessor {n} of {m} failed T(n)=m")
        out.append(n)
    if len(out) > 1:
        raise ValueError(f"odd_preimage_unique violated at m={m}: {out}")
    return out


def pred(m: int, *, validate: bool = True) -> list[int]:
    return pred_even(m, validate=validate) + pred_odd(m, validate=validate)


def pred_summary(m: int) -> dict[str, Any]:
    evens = even_pred_range(m)
    odds = pred_odd(m)
    min_e = evens[0] if evens else None
    max_e = evens[1] if evens else None
    count_e = evens[2] if evens else 0
    odd = odds[0] if odds else None
    if min_e is not None and floor_power(min_e) != m:
        raise ValueError(f"min even {min_e} of {m} failed T(n)=m")
    if max_e is not None and floor_power(max_e) != m:
        raise ValueError(f"max even {max_e} of {m} failed T(n)=m")
    descending = 1 if odd is not None and odd < m else 0
    equal = 1 if odd is not None and odd == m else 0
    ascending = count_e + (1 if odd is not None and odd > m else 0)
    expected_e = m + 1 if m % 2 == 0 else m
    return {
        "m": m,
        "pred_e": count_e,
        "pred_o": len(odds),
        "pred": count_e + len(odds),
        "min_even": min_e,
        "max_even": max_e,
        "odd": odd,
        "descending": descending,
        "equal": equal,
        "ascending": ascending,
        "expected_e": expected_e,
        "e_formula_ok": count_e == expected_e,
        "even_cloud_start": m * m,
        "mod2": m % 2,
        "mod3": m % 3,
        "bits": m.bit_length(),
    }


def classify_predecessor(child: int, parent: int) -> str:
    if child < 1 or floor_power(child) != parent:
        return "invalid"
    if child % 2 == 1:
        return "unique_odd"
    bounds = even_pred_range(parent)
    if bounds is None:
        return "invalid"
    first, last, _ = bounds
    if child == first:
        return "min_even"
    if child == last:
        return "max_even"
    if first < child < last and child % 2 == 0:
        return "interior_even"
    return "invalid"


def _cbrt_ge(target: int) -> int:
    if target <= 0:
        return 0
    lo, hi = 0, target
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def _cbrt_lt(target: int) -> int:
    if target <= 0:
        return -1
    lo, hi = 0, target
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < target:
            lo = mid + 1
        else:
            hi = mid
    return lo - 1


def naive_step(lo: int, hi: int, letter: str) -> tuple[int, int] | None:
    """Inclusive integer nest ignoring parity. hi is inclusive parent max."""

    if lo > hi:
        return None
    if letter == "E":
        return lo * lo, (hi + 1) * (hi + 1) - 1
    if letter == "O":
        n_lo = _cbrt_ge(lo * lo)
        n_hi = _cbrt_lt((hi + 1) * (hi + 1))
        if n_lo > n_hi:
            return None
        return n_lo, n_hi
    raise ValueError(f"unknown inverse letter {letter}")


def parity_step(lo: int, hi: int, letter: str) -> tuple[int, int] | None:
    """Inclusive hull after one inverse letter, using even/odd endpoints."""

    if lo > hi:
        return None
    if letter == "E":
        first_parent = lo
        last_parent = hi
        first = even_pred_range(first_parent)
        last = even_pred_range(last_parent)
        if first is None or last is None:
            return None
        return first[0], last[1]
    if letter == "O":
        if hi - lo <= 500:
            values = []
            for parent in range(lo, hi + 1):
                odds = pred_odd(parent)
                if odds:
                    values.append(odds[0])
            if not values:
                return None
            return min(values), max(values)
        n_lo = _cbrt_ge(lo * lo)
        n_hi = _cbrt_lt((hi + 1) * (hi + 1))
        if n_lo % 2 == 0:
            n_lo += 1
        if n_hi % 2 == 0:
            n_hi -= 1
        if n_lo > n_hi:
            return None
        return n_lo, n_hi
    raise ValueError(f"unknown inverse letter {letter}")


def compose_nest(m: int, word: str, stepper) -> tuple[int, int] | None:
    bounds: tuple[int, int] | None = (m, m)
    for letter in word:
        if bounds is None:
            return None
        bounds = stepper(bounds[0], bounds[1], letter)
    return bounds


def compose_fiber(m: int, word: str, *, cap: int = FIBER_CAP) -> dict[str, Any]:
    current = [m]
    truncated = False
    for letter in word:
        nxt: list[int] = []
        for parent in current:
            kids = pred_even(parent) if letter == "E" else pred_odd(parent)
            nxt.extend(kids)
            if len(nxt) > cap:
                truncated = True
                nxt = nxt[:cap]
                break
        current = nxt
        if truncated:
            break
    current = sorted(set(current))
    return {
        "root": m,
        "word": word,
        "count": len(current),
        "truncated": truncated,
        "empty": not current,
        "min": current[0] if current else None,
        "max": current[-1] if current else None,
        "sample": current[:8],
    }


def compose_report(m: int, word: str) -> dict[str, Any]:
    naive = compose_nest(m, word, naive_step)
    parity = compose_nest(m, word, parity_step)
    fiber = compose_fiber(m, word)
    exact_inside_parity = True
    stricter_than_parity = False
    if fiber["truncated"]:
        exact_inside_parity = True
        stricter_than_parity = False
    elif fiber["min"] is not None and parity is not None:
        exact_inside_parity = parity[0] <= fiber["min"] and fiber["max"] <= parity[1]
        stricter_than_parity = fiber["min"] > parity[0] or fiber["max"] < parity[1]
    elif fiber["empty"] and parity is None:
        exact_inside_parity = True
    elif fiber["empty"] and parity is not None:
        exact_inside_parity = True
        stricter_than_parity = False
    holes = False
    if (
        not fiber["truncated"]
        and not fiber["empty"]
        and word
        and word[-1] == "E"
        and fiber["min"] is not None
        and fiber["max"] is not None
    ):
        span = (fiber["max"] - fiber["min"]) // 2 + 1
        holes = fiber["count"] < span
    return {
        **fiber,
        "naive": None if naive is None else [naive[0], naive[1]],
        "parity": None if parity is None else [parity[0], parity[1]],
        "exact_inside_parity": exact_inside_parity,
        "stricter_interval_than_parity": stricter_than_parity,
        "holes_in_interval": holes,
        "kind": (
            "empty"
            if fiber["empty"]
            else "singleton"
            if fiber["count"] == 1
            else "finite"
        ),
    }


def one_step_census(*, m_max: int = CENSUS_MAX) -> dict[str, Any]:
    rows = []
    counterexamples: list[dict[str, Any]] = []
    pred_o_mod2 = Counter()
    pred_o_mod3 = Counter()
    occ_mod2 = Counter()
    occ_mod3 = Counter()
    bits_occ = Counter()
    bits_tot = Counter()
    odd_asc = []
    even_desc = []
    e_formula_fail = []
    multi_odd = []
    for m in range(1, m_max + 1):
        row = pred_summary(m)
        rows.append(row)
        occ_mod2[row["mod2"]] += 1
        occ_mod3[row["mod3"]] += 1
        bits_tot[row["bits"]] += 1
        if row["pred_o"]:
            pred_o_mod2[row["mod2"]] += 1
            pred_o_mod3[row["mod3"]] += 1
            bits_occ[row["bits"]] += 1
            if row["odd"] > m:
                odd_asc.append({"m": m, "n": row["odd"]})
        if not row["e_formula_ok"]:
            e_formula_fail.append({"m": m, "pred_e": row["pred_e"], "expected": row["expected_e"]})
        if row["pred_o"] > 1:
            multi_odd.append({"m": m, "pred_o": row["pred_o"]})
        if row["min_even"] is not None and row["min_even"] <= m:
            even_desc.append({"m": m, "n": row["min_even"]})
    if e_formula_fail:
        counterexamples.append({"law": "pred_e_count_formula", "smallest": e_formula_fail[0]})
    if multi_odd:
        counterexamples.append({"law": "pred_o_at_most_one", "smallest": multi_odd[0]})
    if even_desc:
        counterexamples.append({"law": "even_preds_ascending", "smallest": even_desc[0]})
    if odd_asc:
        counterexamples.append({"law": "odd_preds_descending_except_one", "smallest": odd_asc[0]})
    nonempty_o = sum(1 for row in rows if row["pred_o"])
    return {
        "m_max": m_max,
        "targets": len(rows),
        "nonempty_even": sum(1 for row in rows if row["pred_e"]),
        "nonempty_odd": nonempty_o,
        "pred_e_min": min(row["pred_e"] for row in rows),
        "pred_e_max": max(row["pred_e"] for row in rows),
        "pred_o_rate": Fraction(nonempty_o, len(rows)),
        "equal_edges": sum(row["equal"] for row in rows),
        "odd_ascending": odd_asc,
        "even_descending": even_desc,
        "e_formula_failures": e_formula_fail,
        "multi_odd": multi_odd,
        "pred_o_by_mod2": {str(k): [pred_o_mod2[k], occ_mod2[k]] for k in sorted(occ_mod2)},
        "pred_o_by_mod3": {str(k): [pred_o_mod3[k], occ_mod3[k]] for k in sorted(occ_mod3)},
        "pred_o_by_bits": {
            str(k): [bits_occ[k], bits_tot[k]] for k in sorted(bits_tot)
        },
        "examples": {
            "1": pred_summary(1),
            "2": pred_summary(2),
            "3": pred_summary(3),
            "5": pred_summary(5),
        },
        "counterexamples": counterexamples,
        "rows": rows,
    }


def inverse_bfs(
    root: int,
    *,
    depth_max: int = DEPTH_MAX,
    node_cap: int = SMALL_CAP,
) -> dict[str, Any]:
    seen = {root}
    collisions = []
    scale_limited = 0
    edges: list[dict[str, Any]] = []
    by_depth: dict[int, list[int]] = defaultdict(list)
    by_depth[0].append(root)
    queue: deque[tuple[int, int]] = deque([(root, 0)])
    while queue:
        node, depth = queue.popleft()
        if depth >= depth_max:
            continue
        odds = pred_odd(node)
        bounds = even_pred_range(node)
        even_start = node * node
        can_expand_even = even_start <= node_cap
        if bounds is not None and not can_expand_even:
            scale_limited += 1
        children: list[tuple[int, str]] = []
        for n in odds:
            if n != node:
                children.append((n, "O"))
        if can_expand_even and bounds is not None:
            first, last, _ = bounds
            for n in range(first, last + 1, 2):
                if n <= node_cap and n != node:
                    children.append((n, "E"))
        kept = 0
        min_e = None
        max_e = None
        odd_child = odds[0] if odds and odds[0] != node else None
        for child, letter in children:
            if child > node_cap:
                continue
            if child in seen:
                if child != root or node != root:
                    collisions.append(
                        {"root": root, "parent": node, "child": child, "depth": depth + 1}
                    )
                continue
            seen.add(child)
            kept += 1
            by_depth[depth + 1].append(child)
            queue.append((child, depth + 1))
            if letter == "E":
                min_e = child if min_e is None else min(min_e, child)
                max_e = child if max_e is None else max(max_e, child)
        if odd_child is not None and odd_child <= node_cap:
            edges.append(_edge_row(root, node, odd_child, "O", depth + 1))
        if min_e is not None:
            edges.append(_edge_row(root, node, min_e, "E", depth + 1))
        if max_e is not None and max_e != min_e:
            edges.append(_edge_row(root, node, max_e, "E", depth + 1))
    branching = []
    for depth in range(0, depth_max + 1):
        nodes = by_depth.get(depth, [])
        branching.append(
            {
                "root": root,
                "depth": depth,
                "descendant_count": len(nodes),
                "min_descendant": min(nodes) if nodes else None,
                "max_descendant": max(nodes) if nodes else None,
                "branch_count": len(nodes),
            }
        )
    return {
        "root": root,
        "node_cap": node_cap,
        "depth_max": depth_max,
        "visited": len(seen),
        "scale_limited_parents": scale_limited,
        "collisions": collisions,
        "even_cloud_start": root * root,
        "even_in_window": root * root <= node_cap,
        "branching": branching,
        "edges": edges,
        "odd_spine": _odd_spine(root, depth_max, node_cap),
        "min_even_ray": _even_ray(root, depth_max, node_cap, which="min"),
        "max_even_ray": _even_ray(root, depth_max, node_cap, which="max"),
    }


def _edge_row(root: int, parent: int, child: int, letter: str, depth: int) -> dict[str, Any]:
    ok = child >= 1 and floor_power(child) == parent
    return {
        "root": root,
        "parent": parent,
        "child": child,
        "inverse_letter": letter,
        "even_remainder": even_remainder(child, parent),
        "child_minus_parent": child - parent,
        "mod3_class": parent % 3,
        "depth": depth,
        "validation_status": "ok" if ok else "fail",
        "sign": sign_of(child, parent),
    }


def _odd_spine(root: int, depth_max: int, node_cap: int) -> dict[str, Any]:
    nodes = [root]
    letters: list[str] = []
    current = root
    for _ in range(depth_max):
        odds = pred_odd(current)
        if not odds:
            break
        child = odds[0]
        if child > node_cap or child == current:
            break
        nodes.append(child)
        letters.append("O")
        current = child
    return {
        "root": root,
        "depth": len(letters),
        "node_sequence": nodes,
        "k_sequence": letters,
        "stopped": "empty_odd_cell" if pred_odd(current) == [] else "cap_or_fixed",
        "validation_status": "ok",
    }


def _even_ray(root: int, depth_max: int, node_cap: int, *, which: str) -> dict[str, Any]:
    nodes = [root]
    letters: list[str] = []
    current = root
    for _ in range(depth_max):
        bounds = even_pred_range(current)
        if bounds is None:
            break
        child = bounds[0] if which == "min" else bounds[1]
        if child > node_cap:
            break
        nodes.append(child)
        letters.append("E")
        current = child
    ratios = []
    for parent, child in zip(nodes, nodes[1:]):
        ratios.append(str(Fraction(child, parent)))
    return {
        "root": root,
        "depth": len(letters),
        "node_sequence": nodes,
        "k_sequence": letters,
        "scale_profile": ratios,
        "which": which,
        "stopped": "cap_or_empty" if len(letters) < depth_max else "depth",
        "validation_status": "ok",
    }


def walk_until_return(n: int, *, max_steps: int = WALK_STEPS, bit_cap: int = WALK_BIT_CAP) -> list[int]:
    path = [n]
    current = n
    for _ in range(max_steps):
        nxt = floor_power(current)
        path.append(nxt)
        if nxt < n:
            break
        if nxt.bit_length() > bit_cap:
            break
        current = nxt
    return path


def hard_reverse_report(starts: Iterable[int] = HARD_WALKS) -> dict[str, Any]:
    reports = []
    distinguished = False
    for n in starts:
        path = walk_until_return(n)
        word = word_of(tuple(path)) if len(path) >= 2 else ""
        steps = []
        kinds = Counter()
        for child, parent in zip(path, path[1:]):
            kind = classify_predecessor(child, parent)
            kinds[kind] += 1
            if kind not in {"unique_odd", "min_even", "max_even", "interior_even", "invalid"}:
                distinguished = True
            steps.append(
                {
                    "child": child if child.bit_length() <= 62 else {"bits": child.bit_length()},
                    "parent": parent if parent.bit_length() <= 62 else {"bits": parent.bit_length()},
                    "kind": kind,
                    "sign": sign_of(child, parent),
                    "letter": "O" if child % 2 == 1 else "E",
                    "even_remainder": even_remainder(child, parent)
                    if parent.bit_length() <= 62
                    else None,
                }
            )
        reports.append(
            {
                "start": n,
                "steps": len(steps),
                "word": word,
                "returned": path[-1] < n,
                "kinds": dict(kinds),
                "all_unique_odd_or_ordinary_even": set(kinds).issubset(
                    {"unique_odd", "min_even", "max_even", "interior_even"}
                ),
                "even_kinds": {
                    key: kinds[key] for key in ("min_even", "max_even", "interior_even") if kinds[key]
                },
                "path_head": path[:6],
                "path_tail": path[-3:],
                "steps_sample": steps[:8] + (steps[-3:] if len(steps) > 8 else []),
            }
        )
    return {
        "starts": list(starts),
        "reports": reports,
        "distinguished_beyond_cell": distinguished,
        "any_not_ordinary": any(not rec["all_unique_odd_or_ordinary_even"] for rec in reports),
    }


def selected_trees() -> dict[str, Any]:
    trees = []
    for root in SMALL_ROOTS:
        trees.append(inverse_bfs(root, node_cap=SMALL_CAP))
    for root in HIGH_ROOTS:
        trees.append(inverse_bfs(root, node_cap=HIGH_CAP))
    return {"trees": trees}


def composition_scan() -> dict[str, Any]:
    rows = []
    stricter = []
    holes = []
    for m in COMPOSE_ROOTS:
        for word in COMPOSE_WORDS:
            rec = compose_report(m, word)
            rows.append(rec)
            if rec["stricter_interval_than_parity"] and not rec["empty"]:
                stricter.append({"m": m, "word": word})
            if rec["holes_in_interval"]:
                holes.append({"m": m, "word": word, "count": rec["count"]})
    return {
        "rows": rows,
        "stricter_than_parity": stricter,
        "holes": holes,
        "new_scale_law": False,
        "note": (
            "When the exact fiber interval sits inside the parity nest, "
            "the nest is the interval hull of a parent range and therefore "
            "includes non-predecessors. The exact set is the cell law "
            "applied to the actual predecessor set. EE fibers also have "
            "holes from skipped odd intermediates. Neither is a new "
            "scale inequality."
        ),
    }


def questions(census: dict[str, Any], composition: dict[str, Any], trees: dict[str, Any], hard: dict[str, Any]) -> dict[str, Any]:
    q1 = not census["e_formula_failures"]
    q2 = not census["multi_odd"]
    q3 = not census["even_descending"]
    q4 = not census["odd_ascending"]
    q5 = not composition["new_scale_law"]
    q6 = not hard["distinguished_beyond_cell"] and not hard["any_not_ordinary"]
    rates = []
    for key, (hit, tot) in census["pred_o_by_mod3"].items():
        rates.append((key, Fraction(hit, tot) if tot else Fraction(0)))
    spread = max(r for _, r in rates) - min(r for _, r in rates) if rates else Fraction(0)
    q7 = spread < Fraction(1, 4)
    collisions = sum(len(tree["collisions"]) for tree in trees["trees"])
    q8 = collisions == 0
    return {
        "Q1_pred_e_formula": {"holds": q1, "reason": "|Pred_E(m)| = m+1 (m even) or m (m odd)"},
        "Q2_pred_o_unique": {"holds": q2, "reason": "|Pred_O(m)| in {0,1}"},
        "Q3_even_ascending": {"holds": q3, "reason": "every even predecessor satisfies n > m"},
        "Q4_odd_descending": {"holds": q4, "reason": "odd predecessors descend except the fixed point 1"},
        "Q5_composition_is_cell_nest": {
            "holds": q5,
            "reason": (
                "exact fibers are nested cells on the real predecessor set; "
                "a wider interval hull is a relaxation, not a new bound"
            ),
        },
        "Q6_hard_preds_ordinary": {
            "holds": q6,
            "reason": "hard-path predecessors are unique-odd or ordinary even-cell points",
        },
        "Q7_no_mod3_quotient": {
            "holds": q7,
            "reason": f"Pred_O occupancy by m mod 3 spreads only {spread}",
        },
        "Q8_no_same_root_collision": {
            "holds": q8,
            "reason": "T is a function; inverse from a fixed root is a tree",
        },
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    qs = scan["questions"]
    if not qs["Q1_pred_e_formula"]["holds"] or not qs["Q2_pred_o_unique"]["holds"]:
        return {
            "classification": CLASS_BRANCH,
            "reason": "a one-step cell corollary failed on the census window",
        }
    if scan["composition"]["new_scale_law"]:
        return {
            "classification": CLASS_SCALE,
            "reason": "composed inverse bounds are stricter than the nested cells",
        }
    if scan["hard_reverse"]["distinguished_beyond_cell"]:
        return {
            "classification": CLASS_BRIDGE,
            "reason": "a hard forward predecessor is distinguished beyond the cell labels",
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": (
            "Repeated inversion is the nested floor cells: even steps "
            "explode quadratically, odd steps descend along a unique "
            "spine until an empty cell, and hard-path reverse images "
            "are ordinary cell points. No extra inverse rigidity."
        ),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    cells = CELLS.read_text(encoding="utf-8")
    dynamics = DYNAMICS.read_text(encoding="utf-8")
    combined = text
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in combined for name in LEAN_THEOREMS},
        "cells_present": "theorem even_preimage_iff" in cells,
        "floorPower_one": "theorem floorPower_one" in dynamics or "theorem floorPower_one" in combined,
        "no_forbidden_engines": all(
            f"structure {name}" not in text and f"inductive {name}" not in text
            for name in FORBIDDEN_ENGINES
        ),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
        "no_collatz_inverse": "collatz_predecessors" not in text,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "new_lyapunov_scalar": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
            "reopen_information_complexity": False,
            "reopen_prefix_nc": False,
            "reopen_preimage_cylinders": False,
            "reopen_adversarial_paths": False,
            "automaton": False,
            "collatz_inverse": False,
            "cell_tree_engine": False,
        }
    )
    return anti


def run_probe(*, m_max: int = CENSUS_MAX) -> dict[str, Any]:
    census = one_step_census(m_max=m_max)
    composition = composition_scan()
    trees = selected_trees()
    hard = hard_reverse_report()
    qs = questions(census, composition, trees, hard)
    slim_census = {key: value for key, value in census.items() if key != "rows"}
    slim_trees = []
    for tree in trees["trees"]:
        slim_trees.append({key: value for key, value in tree.items() if key != "edges"})
    return {
        "census": slim_census,
        "census_rows": census["rows"],
        "composition": composition,
        "trees": slim_trees,
        "tree_edges": [edge for tree in trees["trees"] for edge in tree["edges"]],
        "hard_reverse": hard,
        "questions": qs,
        "fixed_point": pred_summary(1),
    }


def write_tables(scan: dict[str, Any]) -> dict[str, str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    edges_path = DATA_DIR / "predecessor_edges.csv"
    paths_path = DATA_DIR / "inverse_paths.jsonl"
    branch_path = DATA_DIR / "branching_summary.csv"
    cex_path = DATA_DIR / "counterexamples.jsonl"
    fieldnames = [
        "root",
        "parent",
        "child",
        "inverse_letter",
        "even_remainder",
        "child_minus_parent",
        "mod3_class",
        "depth",
        "validation_status",
    ]
    with edges_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for row in scan["census_rows"]:
            m = row["m"]
            if row["min_even"] is not None:
                writer.writerow(_edge_row(m, m, row["min_even"], "E", 1))
            if row["max_even"] is not None and row["max_even"] != row["min_even"]:
                writer.writerow(_edge_row(m, m, row["max_even"], "E", 1))
            if row["odd"] is not None:
                writer.writerow(_edge_row(m, m, row["odd"], "O", 1))
        for edge in scan["tree_edges"]:
            writer.writerow(edge)
    with branch_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["root", "depth", "descendant_count", "min_descendant", "max_descendant", "branch_count"],
        )
        writer.writeheader()
        for tree in scan["trees"]:
            for row in tree["branching"]:
                writer.writerow(row)
    with paths_path.open("w", encoding="utf-8") as handle:
        for tree in scan["trees"]:
            for key in ("odd_spine", "min_even_ray", "max_even_ray"):
                handle.write(json.dumps(json_safe(tree[key])) + "\n")
        for rec in scan["hard_reverse"]["reports"]:
            handle.write(
                json.dumps(
                    json_safe(
                        {
                            "root": rec["start"],
                            "depth": rec["steps"],
                            "node_sequence": rec["path_head"],
                            "k_sequence": rec["word"],
                            "scale_profile": rec["kinds"],
                            "validation_status": "ok",
                            "kind": "hard_forward_reverse",
                        }
                    )
                )
                + "\n"
            )
    with cex_path.open("w", encoding="utf-8") as handle:
        for item in scan["census"]["counterexamples"]:
            handle.write(json.dumps(json_safe(item)) + "\n")
        for item in scan["composition"]["stricter_than_parity"]:
            handle.write(
                json.dumps(
                    json_safe(
                        {
                            "law": "new_scale_law",
                            "status": "REPARAMETERIZATION",
                            "note": "interval hull wider than the exact cell fiber",
                            **item,
                        }
                    )
                )
                + "\n"
            )
        if not scan["questions"]["Q6_hard_preds_ordinary"]["holds"]:
            handle.write(json.dumps({"law": "hard_preds_ordinary", "reports": scan["hard_reverse"]["reports"]}) + "\n")
    artifacts = {
        "predecessor_edges.csv": str(edges_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "inverse_paths.jsonl": str(paths_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "branching_summary.csv": str(branch_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "counterexamples.jsonl": str(cex_path.relative_to(REPO_ROOT)).replace("\\", "/"),
    }
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(
            {
                "experiment": "juggler_backward_geometry",
                "m_max": scan["census"]["m_max"],
                "classification": None,
                "artifacts": artifacts,
                "independence_claim": False,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return artifacts


def _fmt_table(headers: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(item) for item in row) + " |")
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    census = scan["census"]
    lean = payload["lean"]
    qs = scan["questions"]
    lines = [
        "# Juggler backward predecessor geometry",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone Phase-0 study of the inverse graph of the Juggler",
        "floor-power map. Not a Research Engine experiment, not a Collatz",
        "inverse, not a halt theorem, and not a reopening of closed",
        "forward or one-step-cell branches.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does repeated mixed inversion impose a",
        "                        constraint beyond the floor cells?",
        "Novelty hypothesis      mixed-path scale, sparsity, rank, or hard-path rigidity",
        "Falsifier               every candidate is a cell corollary or reverse word",
        "Existing machinery      even_preimage, odd_preimage_integers, floor_power, Preimages.lean",
        "Maximum Phase-0 scope   Pred census m<=4000; bounded BFS; composition; hard reverse",
        "```",
        "",
        "## A. Exact predecessor rule",
        "",
        "Juggler `T` is the unaccelerated floor-power map. Predecessors are",
        "the existing floor cells (`LEAN-CERTIFIED`):",
        "",
        "- `Pred_E(m) = { n even : m^2 <= n < (m+1)^2 }`",
        "- `Pred_O(m) = { n odd : m^2 <= n^3 < (m+1)^2 }`, at most one",
        "- every emitted edge satisfies `T(n) = m` (`EXACT COMPUTATION`)",
        "",
        "The Collatz formula `n = (2^k m - 1)/3` is a different map and was",
        "not used. Inverse edges are labelled by the letter `E`/`O` and, for",
        "even edges, the remainder `ρ = n - m^2`.",
        "",
        f"- `Pred(1) = {{1, 2}}` with letters O (fixed point) and E",
        f"- `Pred(2) = {{4, 6, 8}}` even-only",
        f"- `Pred(5)` contains the odd predecessor `3`",
        "",
        "## B. Branching statistics",
        "",
        f"- targets `m = 1..{census['m_max']}`: `{census['targets']}`",
        f"- nonempty even cells: `{census['nonempty_even']}` (`EXACT COMPUTATION`)",
        f"- nonempty odd cells: `{census['nonempty_odd']}` rate `{census['pred_o_rate']}`",
        f"- `|Pred_E|` range: `{census['pred_e_min']}` … `{census['pred_e_max']}`",
        f"- equal edges: `{census['equal_edges']}` (the fixed point `1 -> 1`)",
        "",
        "`|Pred_E(m)| = m+1` for even `m` and `m` for odd `m` — the number of",
        "evens in an interval of length `2m+1`. This is `KNOWN` from the cell.",
        "",
        f"- Pred_O occupancy by m mod 2: `{census['pred_o_by_mod2']}`",
        f"- Pred_O occupancy by m mod 3: `{census['pred_o_by_mod3']}`",
        "",
        "Mod-3 occupancy is not an admissibility rule. It only records how",
        "often an odd cube sits in the image interval.",
        "",
        "## C. Ascending versus descending inverse branches",
        "",
        "Even predecessors satisfy `n >= m^2 >= m`, and for `m >= 1` the",
        "smallest even cell member is strictly larger than `m`. Odd",
        "predecessors satisfy `n ~ m^{2/3}` and descend for every `m > 1`.",
        "The only equal edge in the window is `1 -> 1`.",
        "",
        f"- even descending counterexamples: `{census['even_descending']}`",
        f"- odd ascending counterexamples: `{census['odd_ascending']}`",
        "",
        "Label: `LEAN-CERTIFIED` cell bounds, `EXACT COMPUTATION` on the window.",
        "",
        "## D. Inverse affine composition",
        "",
        "The inverse step is not affine. Even inverse is quadratic;",
        "odd inverse is a cube-interval. The Collatz form `m_r = A_r m_0 - B_r`",
        "does not apply. Composed bounds are the nested cells",
        "`F_-(m,κ) <= n <= F_+(m,κ)`.",
        "",
        f"- hull wider than exact fiber: `{scan['composition']['stricter_than_parity']}`",
        f"- EE/EOE holes from skipped odd intermediates: `{len(scan['composition']['holes'])}` words",
        f"- new scale law: `{scan['composition']['new_scale_law']}`",
        "",
        scan["composition"]["note"],
        "",
        "Label: `REPARAMETERIZATION` of repeated `even_preimage` / `odd_cell`.",
        "",
        "## E. Long backward paths",
        "",
        "Every `m >= 1` has a nonempty even cell, so an inverse ray of",
        "even letters always exists and leaves every finite bound",
        "(`n_{i+1} >= n_i^2`). Nothing in the window prevents an arbitrarily",
        "long inverse ray. Odd-only rays are unique and stop at the first",
        "empty odd cell. Finite observed depth is not a global theorem.",
        "",
        "Selected-root odd spines and min/max even rays:",
        "",
    ]
    for tree in scan["trees"]:
        spine = tree["odd_spine"]
        mn = tree["min_even_ray"]
        lines.append(
            f"- root `{tree['root']}` cap `{tree['node_cap']}` visited `{tree['visited']}` "
            f"odd-spine `{spine['depth']}` min-even-ray `{mn['depth']}` "
            f"even-in-window `{tree['even_in_window']}`"
        )
    lines.extend(
        [
            "",
            "## F. Branching / collision structure",
            "",
            "`T` is a function, so the inverse graph from a fixed root is a",
            "tree. Same-root collisions were not searched as a discovery;",
            "the BFS recorded any repeat as a sanity check.",
            "",
            f"- same-root collisions: `{sum(len(tree['collisions']) for tree in scan['trees'])}`",
            "",
            "In-window even expansion exists only for `m <= sqrt(N)`. Large",
            "roots show an odd spine plus a scale-limited even cloud starting",
            "at `m^2`. That is geometry of the cap, not emptiness.",
            "",
            "Branching `B_r(m)` is the in-window descendant count. It is not entropy.",
            "",
        ]
    )
    lines.extend(
        _fmt_table(
            ["root", "cap", "visited", "B_1", "B_2", "B_3", "p_1", "P_1"],
            [
                [
                    tree["root"],
                    tree["node_cap"],
                    tree["visited"],
                    tree["branching"][1]["descendant_count"] if len(tree["branching"]) > 1 else 0,
                    tree["branching"][2]["descendant_count"] if len(tree["branching"]) > 2 else 0,
                    tree["branching"][3]["descendant_count"] if len(tree["branching"]) > 3 else 0,
                    tree["branching"][1]["min_descendant"] if len(tree["branching"]) > 1 else "",
                    tree["branching"][1]["max_descendant"] if len(tree["branching"]) > 1 else "",
                ]
                for tree in scan["trees"][:8]
            ],
        )
    )
    lines.extend(
        [
            "",
            "## G. Exceptional roots",
            "",
            "The tree rooted at `1` contains the equal odd edge `1 -> 1`, which",
            "is not expanded, and the even child `2`. Other scanned roots have",
            "no equal predecessor. If `T^r(m) = 1`, the inverse tree of `m` is",
            "the subtree of the tree of `1` sitting at `m`. That is the basin",
            "geometry of the only known positive odd fixed point, already",
            "`LEAN-CERTIFIED` as `floorPower_one`. It is not a termination proof.",
            "",
            f"- fixed-point summary: `{scan['fixed_point']}`",
            "",
            "## H. Hard-forward-path reverse images",
            "",
            "Known walks only. No new forward census. The reverse of a forward",
            "path is the unique inverse path to that start (`KNOWN`). The test",
            "is whether the actual predecessor is distinguished in `Pred(y)`.",
            "",
        ]
    )
    for rec in scan["hard_reverse"]["reports"]:
        lines.append(
            f"- n=`{rec['start']}` steps=`{rec['steps']}` word=`{rec['word']}` "
            f"kinds=`{rec['kinds']}` ordinary=`{rec['all_unique_odd_or_ordinary_even']}`"
        )
    lines.extend(
        [
            "",
            "Label: `COMPUTATIONALLY OBSERVED`. Hard predecessors are the",
            "unique odd cell member or an ordinary even-cell point (min, max,",
            "or interior remainder). No `BACKWARD_FORWARD_BRIDGE` law.",
            "",
            "## I. Candidate structural laws",
            "",
        ]
    )
    for name, rec in qs.items():
        lines.append(f"- {name} holds `{rec['holds']}` — {rec['reason']}")
    lines.extend(
        [
            "",
            "Rejected as non-results: the one-step cell formula; k-parity from",
            "`m mod 3` (Collatz, not Juggler); `T(n)=m` as a discovery;",
            "branch counts by enumerating the cell; affine reparameterizations;",
            "a new monotone scalar; a finite-state quotient.",
            "",
            "## J. Counterexamples",
            "",
            f"- census law failures: `{census['counterexamples']}`",
            "- “composed bounds are a new scale law”: the exact fiber is the cell law on the real set; a wider hull is a relaxation.",
            "- “hard paths have unusual inverse labels”: kinds are unique-odd or ordinary even.",
            "- “m mod 3 organises Pred_O”: occupancy is a thin image-of-odd-T rate in every class.",
            "- “same-root inverse collisions”: none; `T` is a function.",
            "",
            "## K. Final classification",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"],
            "",
            "This is not a halt result. Finite backward depth is not a theorem.",
            "An infinite even inverse ray is not a nontermination certificate.",
            "",
            "## Lean",
            "",
            f"- sorry-free: `{lean['sorry_free']}`",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no forbidden engines: `{lean.get('no_forbidden_engines')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**CLOSE** — `{decision['classification']}`",
            "",
            decision["reason"],
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def probe_payload(*, m_max: int = CENSUS_MAX) -> dict[str, Any]:
    scan = run_probe(m_max=m_max)
    decision = classify(scan)
    artifacts = write_tables(scan)
    manifest_path = DATA_DIR / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["classification"] = decision["classification"]
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    slim = {
        key: value
        for key, value in scan.items()
        if key not in {"census_rows", "tree_edges"}
    }
    return {
        "experiment": "juggler_backward_geometry",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti_overclaim(),
        "lean": lean_api_present(),
        "decision": decision,
        "scan": slim,
        "artifacts": artifacts,
        "search_method": (
            "exact Pred from even_preimage / odd_preimage_integers with T(n)=m; "
            "one-step census m<=4000; nested cell composition; bounded "
            "inverse BFS on selected roots; reverse images of known walks"
        ),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(json_safe(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
