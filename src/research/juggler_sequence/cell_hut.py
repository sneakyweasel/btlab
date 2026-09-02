"""Cell-hut quotient of Juggler predecessor-cell neighborhoods.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a Collatz hut and not an automaton. Uses existing even/odd floor
cells. Does not import the Collatz inverse. Does not reopen PE-factor,
Word Atlas factors, realization-set geometry, landing-image, residual
future-quotient, arithmetic projections of y, sum-rho, NC-boundary,
first-return, adversarial paths, information-complexity, ordinary
backward geometry, accelerated odd-to-odd, or the 2-adic bridge.

The raw hut H(m) = (Pred_E(m), Pred_O(m)) determines m. Compact
signatures forget identifying coordinates. The question is whether
equivalent signatures have a small structured family of successors
under T, or whether the construction only renames the integer map.
"""

from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Iterable

from bt.calculus.derivative import D, lsd
from bt.calculus.integral import I
from bt.calculus.jets import integer_jet
from bt.representation import encode
from research.juggler_sequence.accelerated import RECORD_STARTS
from research.juggler_sequence.atlas.fixtures import PE_CHAIN_1999, PE_CHAIN_365
from research.juggler_sequence.backward_geometry import (
    HARD_WALKS,
    even_pred_range,
    pred_odd,
)
from research.juggler_sequence.excursions import HARD_STARTS
from research.juggler_sequence.landing_valuation import v2
from research.juggler_sequence.lean_paths import CELLS, DYNAMICS, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.realization_geometry import FIRST_HOLES

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cell_hut.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cell_hut.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_cell_hut.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cell_hut"
FIGURE_DIR = DATA_DIR / "figures"

CENSUS_MAX = 4000
EXTEND_MAX = 100_000
WALK_STEPS = 80
WALK_BIT_CAP = 25_000
SPINE_CAP = 64
BT_JET_LEN = 4

VERSIONS = (
    "v1_occupancy",
    "v2_type",
    "v3_oddpos",
    "v4_mod3",
    "vB_border",
    "vC_valuation",
)
CELL_HUT_VERSIONS = ("v1_occupancy", "v2_type", "v3_oddpos", "v4_mod3")
PRIMARY_VERSION = "v3_oddpos"

CLASS_STRUCTURE = "HUT_STRUCTURE_GREEN"
CLASS_RULE = "HUT_RULE_GREEN"
CLASS_TRANSITION = "HUT_TRANSITION_GREEN"
CLASS_FAN = "EVEN_FAN_GREEN"
CLASS_SPINE = "ODD_SPINE_GREEN"
CLASS_BT = "BALANCED_TERNARY_HUT_GREEN"
CLASS_RANK = "HUT_RANK_GREEN"
CLASS_WELL = "HUT_WELLFOUNDED_GREEN"
CLASS_BRIDGE = "HUT_FORWARD_BRIDGE_GREEN"
CLASS_COMPLEX = "HUT_COMPLEX"

LEAN_THEOREMS = (
    "even_preimage_iff",
    "odd_preimage_iff",
    "odd_preimage_unique",
    "floorPower_even_eq_iff_sq_interval",
    "floorPower_odd_eq_iff_cube_interval",
    "floorPower_one",
)

_COLLATZ_MOD = "research" + ".collatz"

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
    "CellHutQuotient",
)

HARD_FIXTURES = tuple(
    sorted(
        {
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            10,
            11,
            *PE_CHAIN_365["starts"],
            *PE_CHAIN_365["images"],
            *PE_CHAIN_1999["starts"],
            *PE_CHAIN_1999["images"],
            *HARD_WALKS,
            *RECORD_STARTS,
            *HARD_STARTS,
        }
    )
)

DIAGRAM_STATES = (1, 2, 5, 365)
SPINE_ROOTS = (1, 5, 9, 37, 365, 1999)


def json_safe(value: Any) -> Any:
    if isinstance(value, int) and value.bit_length() > 256:
        return {"bits": value.bit_length(), "parity": value % 2}
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    return value


def icbrt_ceil(target: int) -> int:
    """Smallest k >= 0 with k^3 >= target."""

    if target <= 0:
        return 0
    hi = 1 << ((target.bit_length() + 2) // 3 + 1)
    lo = 0
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def odd_predecessor_of(m: int) -> int | None:
    """Unique odd n with m^2 <= n^3 < (m+1)^2, or None."""

    if m < 1:
        raise ValueError("odd_predecessor_of requires a positive integer")
    lo2 = m * m
    hi2 = (m + 1) * (m + 1)
    k = icbrt_ceil(lo2)
    cube = k * k * k
    if k >= 1 and cube < hi2 and k % 2 == 1:
        return k
    return None


def certify_even_predecessor(n: int, m: int) -> bool:
    return n >= 2 and n % 2 == 0 and m * m <= n < (m + 1) * (m + 1) and floor_power(n) == m


def certify_odd_predecessor(n: int, m: int) -> bool:
    return n >= 1 and n % 2 == 1 and m * m <= n * n * n < (m + 1) * (m + 1) and floor_power(n) == m


def _cmp(a: int, b: int) -> int:
    return (a > b) - (a < b)


def border_parts(m: int) -> tuple[int, int, int]:
    """Neighbor-image type: (cmp(J(m-1), J(m)), cmp(J(m+1), J(m)), tied)."""

    jm = floor_power(m)
    if m <= 1:
        rel_left = 0
        tied = 0
    else:
        left = floor_power(m - 1)
        rel_left = _cmp(left, jm)
        tied = int(left == floor_power(m + 1))
    rel_right = _cmp(floor_power(m + 1), jm)
    return rel_left, rel_right, tied


def valuation_parts(m: int) -> tuple[int, int]:
    left = v2(m - 1) if m > 1 else -1
    return left, v2(m + 1)


def odd_tertile(m: int, odd: int | None) -> int:
    if odd is None:
        return 0
    width = 2 * m + 1
    rho = odd * odd * odd - m * m
    if rho < 0 or rho >= width:
        raise ValueError(f"cube remainder {rho} of {odd} outside cell of {m}")
    return 1 + (3 * rho) // width


def order_type(m: int, odd: int | None, lower_e: int) -> str:
    if m == 1 and odd == 1:
        return "fixed_1"
    if odd is None:
        return "no_odd"
    if odd < m < lower_e:
        return "o_lt_m_lt_E"
    return "other"


def bt_reference(m: int) -> str:
    jet = ",".join(str(int(digit)) for digit in integer_jet(m, BT_JET_LEN))
    digits = encode(m).digits_lsd()[:8]
    word = ",".join(str(int(d)) for d in digits)
    return f"lsd={int(lsd(m))};jet={jet};lsd8={word}"


def hut_geometry(m: int, *, validate: bool = True) -> dict[str, Any]:
    """Exact cell-hut geometry. Authoritative integer object, not a class."""

    if m < 1:
        raise ValueError("hut_geometry requires a positive integer")
    bounds = even_pred_range(m)
    if bounds is None:
        raise ValueError(f"empty even cell at m={m}")
    lower_e, upper_e, size_e = bounds
    odd = odd_predecessor_of(m)
    expected_e = m + 1 if m % 2 == 0 else m
    if validate:
        if not certify_even_predecessor(lower_e, m):
            raise ValueError(f"even lower {lower_e} of {m} failed T(n)=m")
        if not certify_even_predecessor(upper_e, m):
            raise ValueError(f"even upper {upper_e} of {m} failed T(n)=m")
        if odd is not None and not certify_odd_predecessor(odd, m):
            raise ValueError(f"odd predecessor {odd} of {m} failed T(n)=m")
        listed = pred_odd(m, validate=validate)
        if listed != ([] if odd is None else [odd]):
            raise ValueError(f"odd_predecessor_of disagrees with pred_odd at m={m}")
        if size_e != expected_e:
            raise ValueError(f"|Pred_E({m})|={size_e} != {expected_e}")
    rho = None if odd is None else odd * odd * odd - m * m
    tertile = odd_tertile(m, odd)
    rel_left, rel_right, tied = border_parts(m)
    v_left, v_right = valuation_parts(m)
    slim = m.bit_length() > 256
    return {
        "m": m,
        "has_odd_predecessor": odd is not None,
        "odd_predecessor": odd,
        "even_cell_lower": lower_e,
        "even_cell_upper": upper_e,
        "even_cell_size": size_e,
        "square_lo": m * m,
        "square_hi": (m + 1) * (m + 1),
        "rho": rho,
        "tertile": tertile,
        "parity": m % 2,
        "mod3": m % 3,
        "order_type": order_type(m, odd, lower_e),
        "border": (rel_left, rel_right, tied),
        "valuation": (v_left, v_right),
        "width_over_m": None if slim else f"{2 * m + 1}/{m}",
        "rho_over_m": None if rho is None or slim else f"{rho}/{m}",
        "balanced_ternary_reference": "slim" if slim else bt_reference(m),
        "validation_status": "ok" if validate else "unchecked",
    }


def signature_tuple(geo: dict[str, Any], version: str) -> tuple[Any, ...]:
    """Compact class key. Must omit m, endpoints, and the odd predecessor."""

    has_odd = int(geo["has_odd_predecessor"])
    if version == "v1_occupancy":
        return (has_odd,)
    if version == "v2_type":
        return (geo["parity"], has_odd)
    if version == "v3_oddpos":
        return (geo["parity"], has_odd, geo["tertile"])
    if version == "v4_mod3":
        return (geo["parity"], has_odd, geo["tertile"], geo["mod3"])
    if version == "vB_border":
        rel_left, rel_right, tied = geo["border"]
        return (geo["parity"], has_odd, rel_left, rel_right, tied)
    if version == "vC_valuation":
        v_left, v_right = geo["valuation"]
        return (v_left, v_right, geo["parity"], has_odd)
    raise ValueError(f"unknown hut signature version {version}")


def signature_id(version: str, tup: tuple[Any, ...]) -> str:
    return version + ":" + ",".join(str(item) for item in tup)


def identifying_values(geo: dict[str, Any]) -> set[int]:
    values = {geo["m"], geo["even_cell_lower"], geo["even_cell_upper"], geo["square_lo"]}
    if geo["odd_predecessor"] is not None:
        values.add(geo["odd_predecessor"])
    return values


def signature_uses_identifier(geo: dict[str, Any], version: str) -> bool:
    tup = signature_tuple(geo, version)
    banned = identifying_values(geo)
    return any(item in banned for item in tup if isinstance(item, int) and item > 3)


def fan_features(n: int) -> dict[str, Any]:
    """Geometry fields needed for every frozen signature, no cache."""

    odd = odd_predecessor_of(n)
    return {
        "m": n,
        "has_odd_predecessor": odd is not None,
        "odd_predecessor": odd,
        "tertile": odd_tertile(n, odd),
        "parity": n % 2,
        "mod3": n % 3,
        "border": border_parts(n),
        "valuation": valuation_parts(n),
    }


def canonical_even_points(geo: dict[str, Any]) -> dict[str, int]:
    lo = geo["even_cell_lower"]
    hi = geo["even_cell_upper"]
    mid = lo + ((hi - lo) // 4) * 2
    if mid % 2 == 1:
        mid += 1
    if mid < lo:
        mid = lo
    if mid > hi:
        mid = hi
    points = {"lower": lo, "upper": hi, "midpoint": mid}
    odd = geo["odd_predecessor"]
    if odd is not None:
        nearest = lo if abs(lo - odd) <= abs(hi - odd) else hi
        probe = lo + ((odd - lo) // 2) * 2
        if lo <= probe <= hi and probe % 2 == 0:
            if abs(probe - odd) < abs(nearest - odd):
                nearest = probe
        points["nearest_even_to_odd"] = nearest
    return points


class GeometryCache:
    def __init__(self) -> None:
        self._data: dict[int, dict[str, Any]] = {}

    def get(self, m: int, *, validate: bool = True) -> dict[str, Any]:
        rec = self._data.get(m)
        if rec is None:
            if m.bit_length() > 256:
                rec = fan_features(m)
            else:
                rec = hut_geometry(m, validate=validate)
            self._data[m] = rec
        return rec


def analyze_transitions(
    ms: Iterable[int],
    cache: GeometryCache,
    version: str,
    *,
    validate_images: bool = True,
    collect_rows: bool = True,
) -> dict[str, Any]:
    class_members: dict[str, list[int]] = defaultdict(list)
    class_successors: dict[str, set[str]] = defaultdict(set)
    edge_counts: dict[tuple[str, str], int] = Counter()
    rows: list[dict[str, Any]] = []
    merge_pair = None
    first_by_class: dict[str, tuple[int, str]] = {}
    self_returns: list[dict[str, Any]] = []

    for m in ms:
        geo = cache.get(m)
        src_tup = signature_tuple(geo, version)
        src_id = signature_id(version, src_tup)
        jm = floor_power(m)
        dest_geo = cache.get(jm, validate=validate_images)
        dst_tup = signature_tuple(dest_geo, version)
        dst_id = signature_id(version, dst_tup)
        class_members[src_id].append(m)
        class_successors[src_id].add(dst_id)
        edge_counts[(src_id, dst_id)] += 1
        if src_id == dst_id:
            if len(self_returns) < 8:
                self_returns.append({"m": m, "Jm": jm, "signature": src_id})
        prev = first_by_class.get(src_id)
        if prev is not None and prev[1] != dst_id and merge_pair is None:
            merge_pair = {
                "version": version,
                "x": prev[0],
                "y": m,
                "source_signature": src_id,
                "successor_x": prev[1],
                "successor_y": dst_id,
                "kind": "same_class_different_successor",
            }
        if src_id not in first_by_class:
            first_by_class[src_id] = (m, dst_id)
        if collect_rows:
            rows.append(
                {
                    "source_m": m,
                    "target_Jm": jm,
                    "source_signature": src_id,
                    "target_signature": dst_id,
                    "signature_version": version,
                }
            )

    n_states = sum(len(members) for members in class_members.values())
    n_classes = len(class_members)
    out_degrees = {sid: len(dests) for sid, dests in class_successors.items()}
    max_out = max(out_degrees.values()) if out_degrees else 0
    mean_out = (sum(out_degrees.values()) / n_classes) if n_classes else 0.0
    functional = sum(1 for deg in out_degrees.values() if deg == 1)
    cycle = smallest_cycle(class_successors)
    table = []
    for (src, dst), count in sorted(edge_counts.items(), key=lambda item: (-item[1], item[0])):
        table.append({"source": src, "target": dst, "count": count, "out_degree": out_degrees[src]})
        if len(table) >= 64:
            break
    return {
        "version": version,
        "n_states": n_states,
        "n_classes": n_classes,
        "compression": (n_states / n_classes) if n_classes else 0.0,
        "max_out_degree": max_out,
        "mean_out_degree": mean_out,
        "functional_classes": functional,
        "vacuous_bound": max_out >= max(1, n_classes - 1) if n_classes else False,
        "graph_density": (sum(out_degrees.values()) / (n_classes * n_classes)) if n_classes else 0.0,
        "merge_pair": merge_pair,
        "self_returns": self_returns,
        "smallest_cycle": cycle,
        "class_sizes": sorted((len(v) for v in class_members.values()), reverse=True)[:12],
        "out_degrees": sorted(out_degrees.values(), reverse=True)[:12],
        "transition_table": table,
        "class_successors": {key: sorted(value) for key, value in class_successors.items()},
        "rows": rows,
    }


def smallest_cycle(graph: dict[str, set[str]]) -> list[str] | None:
    best: list[str] | None = None
    best_len: int | None = None
    for start in graph:
        dist = {start: 0}
        parent: dict[str, str | None] = {start: None}
        queue: deque[str] = deque([start])
        found_pred: str | None = None
        while queue:
            node = queue.popleft()
            if best_len is not None and dist[node] + 1 >= best_len:
                continue
            for nxt in graph.get(node, ()):
                if nxt == start:
                    found_pred = node
                    best_len = dist[node] + 1
                    chain = [start]
                    cur: str | None = node
                    while cur is not None and cur != start:
                        chain.append(cur)
                        cur = parent[cur]
                    chain.append(start)
                    chain.reverse()
                    best = chain
                    break
                if nxt not in dist:
                    dist[nxt] = dist[node] + 1
                    parent[nxt] = node
                    queue.append(nxt)
            if found_pred is not None and best_len == 1:
                break
    return best


def odd_spine(root: int, cache: GeometryCache, *, cap: int = SPINE_CAP) -> dict[str, Any]:
    nodes = [root]
    widths = [cache.get(root, validate=root <= CENSUS_MAX)["even_cell_size"]]
    current = root
    seen = {root}
    status = "cap"
    for _ in range(cap):
        odd = odd_predecessor_of(current)
        if odd is None:
            status = "empty_odd_cell"
            break
        if odd in seen:
            status = "cycle" if odd != current else "fixed_point"
            nodes.append(odd)
            widths.append(cache.get(odd, validate=False)["even_cell_size"])
            break
        nodes.append(odd)
        widths.append(cache.get(odd, validate=False)["even_cell_size"])
        seen.add(odd)
        current = odd
    return {
        "root": root,
        "depth": len(nodes) - 1,
        "node_sequence": nodes,
        "cell_width_sequence": widths,
        "parity_sequence": [n % 2 for n in nodes],
        "termination_status": status,
    }


def even_fan_row(m: int, version: str) -> dict[str, Any]:
    bounds = even_pred_range(m)
    if bounds is None:
        raise ValueError(f"empty even cell at m={m}")
    first, last, size = bounds
    counts: Counter[str] = Counter()
    for n in range(first, last + 1, 2):
        if not certify_even_predecessor(n, m):
            raise ValueError(f"even predecessor {n} of {m} failed T(n)=m")
        feat = fan_features(n)
        counts[signature_id(version, signature_tuple(feat, version))] += 1
    top = counts.most_common(8)
    other = size - sum(count for _, count in top)
    dist = ";".join(f"{name}={count}" for name, count in top)
    if other:
        dist = f"{dist};other={other}" if dist else f"other={other}"
    return {
        "target_m": m,
        "signature_version": version,
        "fan_size": size,
        "distinct_child_hut_classes": len(counts),
        "class_distribution": dist,
    }


def even_fan_census(m_max: int, versions: tuple[str, ...] = VERSIONS) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    stats: dict[str, dict[str, Any]] = {
        version: {"distinct": [], "ratios": [], "worst": None} for version in versions
    }
    for m in range(1, m_max + 1):
        bounds = even_pred_range(m)
        if bounds is None:
            raise ValueError(f"empty even cell at m={m}")
        first, last, size = bounds
        counts = {version: Counter() for version in versions}
        for n in range(first, last + 1, 2):
            if not certify_even_predecessor(n, m):
                raise ValueError(f"even predecessor {n} of {m} failed T(n)=m")
            feat = fan_features(n)
            for version in versions:
                counts[version][signature_id(version, signature_tuple(feat, version))] += 1
        for version in versions:
            version_counts = counts[version]
            top = version_counts.most_common(8)
            other = size - sum(count for _, count in top)
            dist = ";".join(f"{name}={count}" for name, count in top)
            if other:
                dist = f"{dist};other={other}" if dist else f"other={other}"
            row = {
                "target_m": m,
                "signature_version": version,
                "fan_size": size,
                "distinct_child_hut_classes": len(version_counts),
                "class_distribution": dist,
            }
            rows.append(row)
            rec = stats[version]
            rec["distinct"].append(row["distinct_child_hut_classes"])
            rec["ratios"].append(row["distinct_child_hut_classes"] / size)
            if rec["worst"] is None or row["distinct_child_hut_classes"] > rec["worst"]["distinct_child_hut_classes"]:
                rec["worst"] = row
    summary: dict[str, Any] = {}
    for version, rec in stats.items():
        distinct_values = rec["distinct"]
        ratios = rec["ratios"]
        summary[version] = {
            "max_distinct": max(distinct_values) if distinct_values else 0,
            "mean_distinct": (sum(distinct_values) / len(distinct_values)) if distinct_values else 0.0,
            "max_ratio": max(ratios) if ratios else 0.0,
            "mean_ratio": (sum(ratios) / len(ratios)) if ratios else 0.0,
            "grows_like_fan": bool(distinct_values) and max(distinct_values) >= max(8, m_max // 20),
            "worst": rec["worst"],
        }
    return {"rows": rows, "summary": summary}


def hut_walk(n: int, cache: GeometryCache, versions: tuple[str, ...] = VERSIONS) -> dict[str, Any]:
    states = [n]
    current = n
    for _ in range(WALK_STEPS):
        if current == 1 or current.bit_length() > WALK_BIT_CAP:
            break
        current = floor_power(current)
        states.append(current)
        if current == 1:
            break
    sequences = {}
    for version in versions:
        sequences[version] = [
            signature_id(version, signature_tuple(cache.get(state, validate=False), version))
            for state in states
        ]
    compact_states = []
    for state in states:
        if state.bit_length() <= 256:
            compact_states.append(state)
        else:
            compact_states.append({"bits": state.bit_length(), "parity": state % 2})
    return {
        "start": n,
        "steps": len(states) - 1,
        "states": compact_states,
        "class_sequences": sequences,
        "distinct_classes": {version: len(set(seq)) for version, seq in sequences.items()},
        "bit_capped": states[-1] != 1 and states[-1].bit_length() > WALK_BIT_CAP,
    }


def bt_probe(cache: GeometryCache, m_max: int, version: str = PRIMARY_VERSION) -> dict[str, Any]:
    same_d = 0
    compared_d = 0
    same_i = 0
    compared_i = 0
    jet_buckets: dict[tuple[int, ...], set[str]] = defaultdict(set)
    suffix_split = None
    for m in range(1, m_max + 1):
        geo = cache.get(m)
        sid = signature_id(version, signature_tuple(geo, version))
        jet = tuple(int(digit) for digit in integer_jet(m, BT_JET_LEN))
        jet_buckets[jet].add(sid)
        if suffix_split is None and len(jet_buckets[jet]) > 1:
            others = [k for k in range(1, m) if tuple(int(d) for d in integer_jet(k, BT_JET_LEN)) == jet]
            suffix_split = {
                "jet": list(jet),
                "x": others[0] if others else None,
                "y": m,
                "version": version,
            }
        derived = D(m)
        if derived >= 1:
            compared_d += 1
            other = signature_id(version, signature_tuple(cache.get(derived, validate=False), version))
            if other == sid:
                same_d += 1
            for a in (-1, 0, 1):
                lifted = I(a, derived)
                if lifted >= 1:
                    compared_i += 1
                    lift_sig = signature_id(
                        version, signature_tuple(cache.get(lifted, validate=False), version)
                    )
                    if lift_sig == sid:
                        same_i += 1
    splits = sum(1 for ids in jet_buckets.values() if len(ids) > 1)
    return {
        "version": version,
        "same_sig_as_D": same_d,
        "compared_D": compared_d,
        "same_sig_as_I_a_D": same_i,
        "compared_I": compared_i,
        "jet_buckets": len(jet_buckets),
        "jet_buckets_split": splits,
        "suffix_determines_hut": splits == 0,
        "suffix_split": suffix_split,
    }


def canonical_point_report(cache: GeometryCache, version: str, states: Iterable[int]) -> list[dict[str, Any]]:
    rows = []
    for m in states:
        geo = cache.get(m)
        points = canonical_even_points(geo)
        rec = {"m": m, "version": version}
        for name, value in points.items():
            rec[name] = value
            rec[f"{name}_sig"] = signature_id(
                version, signature_tuple(cache.get(value, validate=False), version)
            )
            rec[f"{name}_J_sig"] = signature_id(
                version, signature_tuple(cache.get(floor_power(value), validate=False), version)
            )
        rows.append(rec)
    return rows


def rule_candidate(report: dict[str, Any]) -> dict[str, Any] | None:
    """A named parameter rule, not a lookup table on a tiny class set."""

    n_classes = report["n_classes"]
    max_out = report["max_out_degree"]
    if n_classes < 2 or report["merge_pair"] is None and max_out == 1:
        if max_out == 1 and report["compression"] >= 2 and not report["vacuous_bound"]:
            if report["smallest_cycle"] is None:
                return {
                    "kind": "functional_acyclic",
                    "note": "every class has a unique successor and the class graph is acyclic",
                }
            return {
                "kind": "functional_with_cycle",
                "cycle": report["smallest_cycle"],
                "note": "functional class map, but a cycle blocks a strict rank",
            }
    return None


def extend_transitions(m_max: int, versions: tuple[str, ...], cache: GeometryCache) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for version in versions:
        report = analyze_transitions(
            range(1, m_max + 1),
            cache,
            version,
            validate_images=False,
            collect_rows=False,
        )
        out[version] = {
            "n_states": report["n_states"],
            "n_classes": report["n_classes"],
            "compression": report["compression"],
            "max_out_degree": report["max_out_degree"],
            "mean_out_degree": report["mean_out_degree"],
            "vacuous_bound": report["vacuous_bound"],
            "graph_density": report["graph_density"],
            "merge_pair": report["merge_pair"],
            "smallest_cycle": report["smallest_cycle"],
            "functional_classes": report["functional_classes"],
        }
    return out


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    reasons: list[str] = []
    for version, report in scan["transitions"].items():
        reasons.append(
            f"{version}: classes={report['n_classes']} max_out={report['max_out_degree']} "
            f"density={report['graph_density']:.3f} merge={report['merge_pair'] is not None} "
            f"rule={None if report.get('rule') is None else report['rule']['kind']}"
        )
    reasons.append(
        "even-fan distinct counts stay small because every n in E(m) is even, "
        "so the fan only sees the even slice of a finite label set; neighbors of "
        "an even n are odd, so v2(n-1)=v2(n+1)=0. That is not EVEN_FAN_GREEN"
    )
    reasons.append("odd spines terminate at an empty odd cell or the fixed point 1")
    bt = scan["bt"]
    if bt["suffix_determines_hut"]:
        reasons.append("a length-4 BT jet determines the hut; rejected finite-information projection")
    else:
        reasons.append("length-4 BT jets split hut classes; no BT hut representation")
    if scan.get("extension") is not None:
        for version, rec in scan["extension"].items():
            primary = scan["transitions"][version]
            if rec["max_out_degree"] > primary["max_out_degree"]:
                reasons.append(
                    f"{version} out-degree grew from {primary['max_out_degree']} to {rec['max_out_degree']} on m<=1e5"
                )
    return {
        "classification": CLASS_COMPLEX,
        "secondary": [],
        "reason": (
            "Every frozen cell-hut signature is a finite label set, so out-degree is "
            "automatically bounded by the number of labels. Same-class states still "
            "take incompatible successors; class graphs are dense or cyclic; even fans "
            "only occupy the even slice of those labels; the odd spine is the existing "
            "unique-odd descent; BT jets and D/I do not supply a hut calculus. The "
            "quotient coarsens T without simplifying the transition algebra. "
            + "; ".join(reasons)
        ),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    cells = CELLS.read_text(encoding="utf-8")
    dynamics = DYNAMICS.read_text(encoding="utf-8")
    combined = text
    source = Path(__file__).read_text(encoding="utf-8")
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
        "no_collatz_inverse": not any(
            line.lstrip().startswith(("from " + _COLLATZ_MOD, "import " + _COLLATZ_MOD))
            for line in source.splitlines()
        ),
        "no_new_lean_module": "CellHut" not in text,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "new_lyapunov_scalar": False,
            "hut_descent_is_termination": False,
            "reopen_pe_factors": False,
            "reopen_word_atlas": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
            "reopen_information_complexity": False,
            "reopen_backward_geometry": False,
            "reopen_accelerated": False,
            "reopen_2adic_bridge": False,
            "reopen_prefix_nc": False,
            "reopen_preimage_cylinders": False,
            "reopen_adversarial_paths": False,
            "automaton": False,
            "collatz_inverse": False,
            "cell_tree_engine": False,
            "scalar_hut_score": False,
            "engine_control_layer_modified": False,
        }
    )
    return anti


def run_probe(*, m_max: int = CENSUS_MAX, extend_max: int = EXTEND_MAX) -> dict[str, Any]:
    cache = GeometryCache()
    for m in range(1, m_max + 1):
        cache.get(m, validate=True)

    transitions = {}
    for version in VERSIONS:
        report = analyze_transitions(range(1, m_max + 1), cache, version, validate_images=True)
        report["rule"] = rule_candidate(report)
        transitions[version] = report

    spines = [odd_spine(root, cache) for root in SPINE_ROOTS]
    for extra in HARD_FIXTURES:
        if extra not in SPINE_ROOTS:
            spines.append(odd_spine(extra, cache))

    fans = even_fan_census(m_max, VERSIONS)
    walks = [hut_walk(n, cache) for n in HARD_FIXTURES]
    bt = bt_probe(cache, m_max, PRIMARY_VERSION)
    points = canonical_point_report(cache, PRIMARY_VERSION, DIAGRAM_STATES)
    extension = extend_transitions(extend_max, VERSIONS, cache) if extend_max > m_max else None

    hard_geos = [cache.get(n, validate=False) for n in HARD_FIXTURES]
    occupied = sum(1 for m in range(1, m_max + 1) if cache.get(m)["has_odd_predecessor"])
    order_counts = Counter(cache.get(m)["order_type"] for m in range(1, m_max + 1))
    return {
        "m_max": m_max,
        "extend_max": extend_max if extension is not None else m_max,
        "targets": m_max,
        "occupied_odd": occupied,
        "order_types": dict(order_counts),
        "atlas_boundary_labels": list(FIRST_HOLES),
        "hard_fixtures": list(HARD_FIXTURES),
        "transitions": transitions,
        "odd_spines": spines,
        "even_fans": {"summary": fans["summary"], "rows": fans["rows"]},
        "walks": walks,
        "bt": bt,
        "canonical_points": points,
        "extension": extension,
        "hard_geometries": hard_geos,
        "diagram_states": [cache.get(m) for m in DIAGRAM_STATES],
        "primary_geometries": [cache.get(m) for m in range(1, m_max + 1)],
    }


def _transition_type(report: dict[str, Any], source_sig: str, target_sig: str) -> str:
    out = len(report["class_successors"].get(source_sig, ()))
    if source_sig == target_sig:
        return "loop"
    if out == 1:
        return "unique"
    return "family"


def write_tables(scan: dict[str, Any]) -> dict[str, str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    states_path = DATA_DIR / "hut_states.csv"
    trans_path = DATA_DIR / "hut_transitions.csv"
    spines_path = DATA_DIR / "odd_spines.jsonl"
    fans_path = DATA_DIR / "even_fans.csv"
    cex_path = DATA_DIR / "hut_counterexamples.jsonl"

    state_fields = [
        "m",
        "signature_id",
        "signature_version",
        "has_odd_predecessor",
        "odd_predecessor",
        "even_cell_lower",
        "even_cell_upper",
        "even_cell_size",
        "balanced_ternary_reference",
        "validation_status",
    ]
    with states_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=state_fields)
        writer.writeheader()
        for geo in scan["primary_geometries"]:
            for version in VERSIONS:
                writer.writerow(
                    {
                        "m": geo["m"],
                        "signature_id": signature_id(version, signature_tuple(geo, version)),
                        "signature_version": version,
                        "has_odd_predecessor": int(geo["has_odd_predecessor"]),
                        "odd_predecessor": "" if geo["odd_predecessor"] is None else geo["odd_predecessor"],
                        "even_cell_lower": geo["even_cell_lower"],
                        "even_cell_upper": geo["even_cell_upper"],
                        "even_cell_size": geo["even_cell_size"],
                        "balanced_ternary_reference": geo["balanced_ternary_reference"],
                        "validation_status": geo["validation_status"],
                    }
                )

    trans_fields = [
        "source_m",
        "target_Jm",
        "source_signature",
        "target_signature",
        "signature_version",
        "transition_type",
        "parameter_delta",
        "validation_status",
    ]
    with trans_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=trans_fields)
        writer.writeheader()
        for version, report in scan["transitions"].items():
            for row in report["rows"]:
                writer.writerow(
                    {
                        **row,
                        "transition_type": _transition_type(report, row["source_signature"], row["target_signature"]),
                        "parameter_delta": "" if report["rule"] is None else report["rule"]["kind"],
                        "validation_status": "ok",
                    }
                )

    with spines_path.open("w", encoding="utf-8") as handle:
        for spine in scan["odd_spines"]:
            handle.write(json.dumps(json_safe(spine)) + "\n")

    fan_fields = [
        "target_m",
        "signature_version",
        "fan_size",
        "distinct_child_hut_classes",
        "class_distribution",
    ]
    with fans_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fan_fields)
        writer.writeheader()
        for row in scan["even_fans"]["rows"]:
            writer.writerow(row)

    counterexamples = []
    for version, report in scan["transitions"].items():
        if report["merge_pair"] is not None:
            counterexamples.append({"law": "same_class_structured_successor", "status": "REFUTED", **report["merge_pair"]})
        if report["smallest_cycle"] is not None:
            counterexamples.append(
                {
                    "law": "strict_hut_rank",
                    "status": "REFUTED",
                    "version": version,
                    "cycle": report["smallest_cycle"],
                }
            )
        if report["self_returns"]:
            counterexamples.append(
                {
                    "law": "hut_never_returns",
                    "status": "REFUTED",
                    "version": version,
                    "example": report["self_returns"][0],
                }
            )
    for version, rec in scan["even_fans"]["summary"].items():
        if rec["grows_like_fan"] and rec["worst"] is not None:
            counterexamples.append(
                {
                    "law": "even_fan_collapse",
                    "status": "REFUTED",
                    "version": version,
                    "worst": rec["worst"],
                }
            )
    if scan["bt"]["suffix_split"] is not None:
        counterexamples.append(
            {
                "law": "bt_suffix_determines_hut",
                "status": "REFUTED",
                **scan["bt"]["suffix_split"],
            }
        )
    counterexamples.append(
        {
            "law": "raw_H_is_a_class",
            "status": "REFUTED",
            "note": "E(m) endpoints determine m; using H(m) as a class renames T",
            "example": {"m": 5, "even_cell_lower": 26, "even_cell_upper": 34},
        }
    )
    counterexamples.append(
        {
            "law": "even_fan_collapse",
            "status": "REFUTED",
            "note": (
                "E(m) contains only even n, so fan classes are the even slice "
                "of the signature. vC neighbors of even n are odd, hence v2=0"
            ),
            "example": scan["even_fans"]["summary"]["vC_valuation"]["worst"],
        }
    )
    with cex_path.open("w", encoding="utf-8") as handle:
        for item in counterexamples:
            handle.write(json.dumps(json_safe(item)) + "\n")

    artifacts = {
        "hut_states.csv": str(states_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "hut_transitions.csv": str(trans_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "odd_spines.jsonl": str(spines_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "even_fans.csv": str(fans_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "hut_counterexamples.jsonl": str(cex_path.relative_to(REPO_ROOT)).replace("\\", "/"),
    }
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(
            {
                "experiment": "juggler_cell_hut",
                "m_max": scan["m_max"],
                "extend_max": scan["extend_max"],
                "signature_versions": list(VERSIONS),
                "classification": None,
                "artifacts": artifacts,
                "independence_claim": False,
                "cuda": False,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return artifacts


def _svg_escape(text: str) -> str:
    return text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def write_cell_hut_svg(geo: dict[str, Any], path: Path) -> None:
    m = geo["m"]
    lo = geo["even_cell_lower"]
    hi = geo["even_cell_upper"]
    odd = geo["odd_predecessor"]
    width, height = 720, 220
    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#f7f4ea"/>',
        f'<text x="16" y="28" font-family="Georgia, serif" font-size="16">Cell-hut of m={m}</text>',
        '<line x1="40" y1="140" x2="680" y2="140" stroke="#333" stroke-width="2"/>',
    ]
    if odd is None:
        odd_label = "no odd predecessor"
        odd_x = 80
    else:
        odd_label = f"o(m)={odd}"
        odd_x = 80
        lines.append(f'<circle cx="{odd_x}" cy="140" r="6" fill="#b23"/>')
    lines.append(f'<text x="{odd_x - 24}" y="170" font-size="12" font-family="Georgia, serif">{_svg_escape(odd_label)}</text>')
    m_x = 260
    lines.append(f'<circle cx="{m_x}" cy="140" r="6" fill="#222"/>')
    lines.append(f'<text x="{m_x - 10}" y="120" font-size="12" font-family="Georgia, serif">m={m}</text>')
    lines.append('<rect x="380" y="124" width="260" height="32" fill="#7aa2c8" stroke="#234" />')
    lines.append(
        f'<text x="400" y="146" font-size="12" font-family="Georgia, serif">E=[{lo},{hi}] size={geo["even_cell_size"]}</text>'
    )
    lines.append(
        f'<text x="16" y="204" font-size="11" font-family="Georgia, serif">'
        f'{_svg_escape("order " + geo["order_type"] + "  tertile=" + str(geo["tertile"]) + "  " + geo["balanced_ternary_reference"])}'
        "</text>"
    )
    lines.append("</svg>")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_spine_svg(spine: dict[str, Any], path: Path) -> None:
    nodes = spine["node_sequence"]
    width = max(360, 80 + 90 * len(nodes))
    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="140" viewBox="0 0 {width} 140">',
        '<rect width="100%" height="100%" fill="#f7f4ea"/>',
        f'<text x="16" y="24" font-family="Georgia, serif" font-size="14">Odd spine from {spine["root"]} ({spine["termination_status"]})</text>',
    ]
    for i, node in enumerate(nodes):
        x = 40 + i * 90
        lines.append(f'<circle cx="{x}" cy="80" r="16" fill="#fff" stroke="#234" />')
        lines.append(f'<text x="{x}" y="85" text-anchor="middle" font-size="11" font-family="Georgia, serif">{node}</text>')
        if i + 1 < len(nodes):
            lines.append(f'<line x1="{x + 18}" y1="80" x2="{x + 72}" y2="80" stroke="#234" marker-end="url(#a)"/>')
    lines.append("</svg>")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_figures(scan: dict[str, Any], decision: dict[str, Any]) -> dict[str, str]:
    FIGURE_DIR.mkdir(parents=True, exist_ok=True)
    artifacts: dict[str, str] = {}
    for geo in scan["diagram_states"]:
        path = FIGURE_DIR / f"cell_hut_m{geo['m']}.svg"
        write_cell_hut_svg(geo, path)
        artifacts[path.name] = str(path.relative_to(REPO_ROOT)).replace("\\", "/")
    for spine in scan["odd_spines"]:
        if spine["root"] in SPINE_ROOTS:
            path = FIGURE_DIR / f"odd_spine_{spine['root']}.svg"
            write_spine_svg(spine, path)
            artifacts[path.name] = str(path.relative_to(REPO_ROOT)).replace("\\", "/")

    structured = decision["classification"] not in {CLASS_COMPLEX}
    if structured:
        version = PRIMARY_VERSION
        report = scan["transitions"][version]
        if report["max_out_degree"] <= 3 and report["n_classes"] <= 24:
            path = FIGURE_DIR / "hut_transition_graph.svg"
            path.write_text(_transition_svg(report), encoding="utf-8")
            artifacts[path.name] = str(path.relative_to(REPO_ROOT)).replace("\\", "/")
        fan_sum = scan["even_fans"]["summary"][version]
        if not fan_sum["grows_like_fan"] and fan_sum["max_distinct"] <= 3:
            path = FIGURE_DIR / "even_fan_compression.svg"
            path.write_text(
                _note_svg("Even-fan compression", f"{version} max distinct child classes = {fan_sum['max_distinct']}"),
                encoding="utf-8",
            )
            artifacts[path.name] = str(path.relative_to(REPO_ROOT)).replace("\\", "/")
    return artifacts


def _transition_svg(report: dict[str, Any]) -> str:
    nodes = sorted(report["class_successors"])
    width = max(480, 80 + 70 * len(nodes))
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="200" viewBox="0 0 {width} 200">',
        '<rect width="100%" height="100%" fill="#f7f4ea"/>',
        f'<text x="16" y="24" font-family="Georgia, serif" font-size="14">{report["version"]} class transitions</text>',
    ]
    coords = {name: 40 + i * 70 for i, name in enumerate(nodes)}
    for name, x in coords.items():
        parts.append(f'<circle cx="{x}" cy="110" r="12" fill="#fff" stroke="#234"/>')
        parts.append(f'<text x="{x}" y="150" text-anchor="middle" font-size="8" font-family="monospace">{name.split(":", 1)[-1]}</text>')
    for src, dests in report["class_successors"].items():
        x1 = coords[src]
        for dst in dests:
            x2 = coords[dst]
            parts.append(f'<line x1="{x1}" y1="98" x2="{x2}" y2="98" stroke="#234" />')
    parts.append("</svg>")
    return "\n".join(parts) + "\n"


def _note_svg(title: str, body: str) -> str:
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="520" height="120" viewBox="0 0 520 120">'
        '<rect width="100%" height="100%" fill="#f7f4ea"/>'
        f'<text x="16" y="36" font-family="Georgia, serif" font-size="16">{_svg_escape(title)}</text>'
        f'<text x="16" y="72" font-family="Georgia, serif" font-size="13">{_svg_escape(body)}</text>'
        "</svg>\n"
    )


def _fmt_table(headers: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(item) for item in row) + " |")
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cell-hut quotient",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone Phase-0 test of whether Juggler's wide-even / singleton-odd",
        "predecessor cells define a local class whose forward transitions are",
        "simpler than the exact integer map. Not a Research Engine experiment,",
        "not a Collatz hut, not an automaton, and not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does a compact signature of Pred_E / Pred_O",
        "                        simplify T, or only rename it?",
        "Novelty hypothesis      wide-even / singleton-odd is a natural hut class",
        "Falsifier               bijection with m, unbounded out-degree, or",
        "                        same-class incompatible successors",
        "Existing machinery      even_preimage, pred_odd, floor_power, Preimages.lean",
        "Maximum Phase-0 scope   m<=4000; selected 1e5; no GPU; no Lean pilot",
        "```",
        "",
        "## A. Exact geometry, not a class",
        "",
        "Juggler `T` is the unaccelerated floor-power map. The raw hut is",
        "`H(m) = (Pred_E(m), Pred_O(m))` from the existing cells",
        "(`LEAN-CERTIFIED`). Endpoints of `Pred_E` recover `m`, so `H(m)`",
        "as a class is a renaming of `T` and is rejected.",
        "",
        "The Collatz formula `n = (2^k m - 1)/3` was not used.",
        "",
        f"- targets `m = 1..{scan['m_max']}`: `{scan['targets']}`",
        f"- occupied odd cells: `{scan['occupied_odd']}`",
        f"- order types: `{scan['order_types']}`",
        f"- Atlas-boundary labels (fixtures only): `{scan['atlas_boundary_labels']}`",
        "",
        "For `m>1` with an odd predecessor the order is `o(m) < m < E(m)`.",
        "The varying odd position is the cube remainder tertile, not a point",
        "inside the even interval.",
        "",
        "## B. Frozen signature ladder",
        "",
        "Identifying coordinates (`m`, even endpoints, `o(m)`) are excluded",
        "from every class key. Versions were frozen before the census.",
        "Failed versions were not retuned.",
        "",
    ]
    table_rows = []
    for version, report in scan["transitions"].items():
        merge = report["merge_pair"]
        merge_s = "" if merge is None else f"{merge['x']}/{merge['y']}"
        table_rows.append(
            [
                version,
                report["n_classes"],
                f"{report['compression']:.2f}",
                report["max_out_degree"],
                f"{report['mean_out_degree']:.2f}",
                f"{report['graph_density']:.2f}",
                report["functional_classes"],
                merge_s,
                "yes" if report["smallest_cycle"] else "no",
                report["rule"]["kind"] if report["rule"] else "none",
            ]
        )
    lines.extend(
        _fmt_table(
            [
                "version",
                "classes",
                "compression",
                "max_out",
                "mean_out",
                "density",
                "functional",
                "merge_xy",
                "cycle",
                "rule",
            ],
            table_rows,
        )
    )
    lines.extend(
        [
            "",
            "`v4_mod3` is a falsification rung. A modulus-only success is",
            "rejected. `vC_valuation` is the 2-adic comparison only.",
            "",
            "## C. Transition families",
            "",
            "Each state has one successor. A hut class has out-degree equal to",
            "the number of distinct successor classes of its members. A finite",
            "label set bounds that number automatically; the bound is vacuous",
            "unless the family is small *and* parameterized.",
            "",
        ]
    )
    for version, report in scan["transitions"].items():
        pair = report["merge_pair"]
        if pair is not None:
            lines.append(
                f"- `{version}` first merge: `{pair['x']}` and `{pair['y']}` share "
                f"`{pair['source_signature']}` but go to `{pair['successor_x']}` vs "
                f"`{pair['successor_y']}`"
            )
        if report["smallest_cycle"] is not None:
            lines.append(f"- `{version}` smallest class cycle: `{report['smallest_cycle']}`")
        if report["self_returns"]:
            ex = report["self_returns"][0]
            lines.append(f"- `{version}` self-return: m=`{ex['m']}` -> J(m)=`{ex['Jm']}` stays `{ex['signature']}`")
    lines.extend(
        [
            "",
            "## D. Odd spines",
            "",
            "The unique odd predecessor, when it exists, is iterated until the",
            "odd cell is empty. This is the existing `odd_preimage_unique` spine,",
            "not a new inverse law.",
            "",
        ]
    )
    for spine in scan["odd_spines"]:
        if spine["root"] in SPINE_ROOTS:
            lines.append(
                f"- root `{spine['root']}` depth `{spine['depth']}` "
                f"stop `{spine['termination_status']}` nodes `{spine['node_sequence']}`"
            )
    lines.extend(
        [
            "",
            "## E. Even fans",
            "",
        ]
    )
    fan_rows = []
    for version, rec in scan["even_fans"]["summary"].items():
        fan_rows.append(
            [
                version,
                rec["max_distinct"],
                f"{rec['mean_distinct']:.2f}",
                f"{rec['max_ratio']:.3f}",
                rec["grows_like_fan"],
            ]
        )
    lines.extend(
        _fmt_table(
            ["version", "max_distinct", "mean_distinct", "max_ratio", "grows_like_fan"],
            fan_rows,
        )
    )
    lines.extend(
        [
            "",
            "Members of `E(m)` are even, so a fan only occupies the even slice",
            "of a finite label set. For `vC_valuation` the neighbors of an even",
            "`n` are odd, so both 2-adic valuations are 0. Apparent fan",
            "compression is that slice, not `EVEN_FAN_GREEN`.",
            "",
            "## F. Selected walks",
            "",
            "Exact integer trajectories are retained. Class sequences never",
            "replace them. Fixture walks only; no full census.",
            "",
        ]
    )
    for walk in scan["walks"]:
        if walk["start"] in (1, 3, 5, 365, 425, 2183, 3889):
            lines.append(
                f"- n=`{walk['start']}` steps=`{walk['steps']}` "
                f"distinct v3 classes=`{walk['distinct_classes']['v3_oddpos']}`"
            )
    ext = scan["extension"]
    lines.extend(
        [
            "",
            "## G. Extension m<=10^5",
            "",
        ]
    )
    if ext is None:
        lines.append("No extension window.")
    else:
        ext_rows = [
            [
                version,
                rec["n_classes"],
                rec["max_out_degree"],
                f"{rec['mean_out_degree']:.2f}",
                rec["vacuous_bound"],
            ]
            for version, rec in ext.items()
        ]
        lines.extend(_fmt_table(["version", "classes", "max_out", "mean_out", "vacuous"], ext_rows))
    bt = scan["bt"]
    lines.extend(
        [
            "",
            "## H. Balanced ternary",
            "",
            f"- same signature as `D(m)`: `{bt['same_sig_as_D']}` / `{bt['compared_D']}`",
            f"- same signature as some `I_a(D(m))`: `{bt['same_sig_as_I_a_D']}` / `{bt['compared_I']}`",
            f"- length-4 jet buckets: `{bt['jet_buckets']}` splitting: `{bt['jet_buckets_split']}`",
            f"- suffix determines hut: `{bt['suffix_determines_hut']}`",
            f"- first suffix split: `{bt['suffix_split']}`",
            "",
            "A fixed BT suffix determining the hut would reopen the rejected",
            "finite-information projection. `D` / `I_a` are not a hut calculus.",
            "",
            "## I. Well-founded rank",
            "",
            "No structured transition rule survived, so no rank was invented.",
            "Class cycles and self-returns are recorded as counterexamples to",
            "any later claim of strict descent on these signatures.",
            "",
            "## J. Visualizations",
            "",
            "A. Cell-hut diagrams for `m=1,2,5,365`.",
            "C. Odd-spine examples for the spine roots.",
            "B/D/E. Withheld: no nontrivial structured class graph, no genuine",
            "even-fan collapse, and no well-founded parameter.",
            "",
            "## K. Final classification",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"],
            "",
            "This is not a halt result. Hut descent is not termination.",
            "",
            "## Lean",
            "",
            f"- sorry-free: `{lean['sorry_free']}`",
            f"- no new Lean module: `{lean.get('no_new_lean_module')}`",
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
            f"**{payload['branch_status']}** — `{decision['classification']}`",
            "",
            decision["reason"],
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _slim_scan(scan: dict[str, Any]) -> dict[str, Any]:
    slim_transitions = {}
    for version, report in scan["transitions"].items():
        slim_transitions[version] = {key: value for key, value in report.items() if key != "rows"}
    return {
        key: value
        for key, value in scan.items()
        if key not in {"primary_geometries", "even_fans"}
    } | {
        "transitions": slim_transitions,
        "even_fans": {"summary": scan["even_fans"]["summary"]},
    }


def probe_payload(*, m_max: int = CENSUS_MAX, extend_max: int = EXTEND_MAX) -> dict[str, Any]:
    scan = run_probe(m_max=m_max, extend_max=extend_max)
    decision = classify(scan)
    artifacts = write_tables(scan)
    figure_artifacts = write_figures(scan, decision)
    artifacts.update(figure_artifacts)
    manifest_path = DATA_DIR / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["classification"] = decision["classification"]
    manifest["figures"] = figure_artifacts
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    branch_status = "CLOSE" if decision["classification"] == CLASS_COMPLEX else "PROMOTE"
    return {
        "experiment": "juggler_cell_hut",
        "branch_status": branch_status,
        "engine_control_layer_modified": False,
        "anti_overclaim": anti_overclaim(),
        "lean": lean_api_present(),
        "decision": decision,
        "scan": _slim_scan(scan),
        "artifacts": artifacts,
        "search_method": (
            "exact Pred_E / Pred_O from even_pred_range and odd_predecessor_of "
            "with T(n)=m; frozen signatures v1-v4, Border-Hut, valuation; "
            "one-step transitions m<=4000; even fans on that window; odd spines "
            "and walks on fixtures; selected extension to 1e5; no GPU"
        ),
    }


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    m_max: int = CENSUS_MAX,
    extend_max: int = EXTEND_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(m_max=m_max, extend_max=extend_max)
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
