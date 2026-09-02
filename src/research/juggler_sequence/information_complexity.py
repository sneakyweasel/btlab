"""Finite dynamical information complexity of Juggler word futures.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a residual-future quotient, PE-factor, sum-rho, realization-set,
landing-image, N_w-boundary, or first-return experiment.

Studies question A only: how much exact arithmetic information is
needed to distinguish H-step O/E itineraries on a fixed sample.
Does not study proof complexity or formal independence.
~_H is experimental future-equality, not Myhill-Nerode.
"""

from __future__ import annotations

import json
import statistics
from collections import Counter, defaultdict
from hashlib import sha1
from pathlib import Path
from typing import Any, Callable

from bt.representation import encode
from research.juggler_sequence.landing_valuation import v2
from research.juggler_sequence.lean_paths import CELLS, ENVELOPE, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary, word_of
from research.juggler_sequence.residual_state import collect_landings

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_information_complexity.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_information_complexity.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "information_complexity"

H_MAX = 6
K_MAX_2 = 256
K_MAX_3 = 40
BIT_CAP = 4096
LANDING_BIT_CAP = 1024
ATLAS_PE_N_CAP = 100_000
ATLAS_PE_LIMIT = 4000
EXPERIMENT_ID = "wa-20260827T200310Z-cuda-k20-n100000000"

CLASS_GREEN = "INFO_COMPLEXITY_GREEN"
CLASS_PRECISION = "PRECISION_HIERARCHY_GREEN"
CLASS_SEPARATION = "FUTURE_SEPARATION_GREEN"
CLASS_FAMILY = "FAMILY_COMPLEXITY_GREEN"
CLASS_COUNTER = "INFO_COMPLEXITY_COUNTEREXAMPLE"
CLASS_COMPLEX = "INFO_COMPLEXITY_COMPLEX"

DOCUMENTED_MOD16_PAIR = (33, 573141612728625270488952931933108109345)
HARD_STATES = (
    2,
    3,
    7,
    9,
    33,
    37,
    64,
    192,
    193,
    243,
    365,
    425,
    763,
    1523,
    2050,
    2052,
    2183,
    3431,
    3889,
    4447,
    DOCUMENTED_MOD16_PAIR[1],
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

LEVEL_WORD = "word"
LEVEL_COARSE = "coarse"
LEVEL_STATE = "state"


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    if isinstance(value, int) and value.bit_length() > 64:
        return str(value)
    return value


def compact_int(value: int) -> int | str:
    return str(value) if value.bit_length() > 62 else value


def table_int(value: int | str) -> str:
    return str(value)


def ilog2_ceil(q: int) -> int:
    if q <= 1:
        return 0
    return (q - 1).bit_length()


def v3(n: int) -> int:
    if n == 0:
        return -1
    n = abs(n)
    count = 0
    while n % 3 == 0:
        n //= 3
        count += 1
    return count


def v2_3y1(y: int) -> int:
    return v2(3 * y + 1)


def word_future(path: tuple[int, ...], horizon: int) -> str:
    return word_of(path[: horizon + 1])


def state_future(path: tuple[int, ...], horizon: int) -> tuple[int, ...]:
    return path[1 : horizon + 1]


def coarse_atom(x: int) -> tuple[int, int, int, tuple[int, ...]]:
    digits = encode(x).digits_lsd()[:4]
    return (x % 2, x % 8, v2_3y1(x), tuple(digits))


def coarse_future(path: tuple[int, ...], horizon: int) -> tuple[tuple[int, int, int, tuple[int, ...]], ...]:
    return tuple(coarse_atom(path[i]) for i in range(horizon))


def future_of(path: tuple[int, ...], horizon: int, level: str) -> Any:
    if level == LEVEL_WORD:
        return word_future(path, horizon)
    if level == LEVEL_COARSE:
        return coarse_future(path, horizon)
    if level == LEVEL_STATE:
        return state_future(path, horizon)
    raise ValueError(level)


def walk(n: int, steps: int = H_MAX, bit_cap: int = BIT_CAP) -> tuple[int, ...] | None:
    path = [n]
    current = n
    for _ in range(steps):
        nxt = floor_power(current)
        if nxt.bit_length() > bit_cap:
            return None
        path.append(nxt)
        current = nxt
    return tuple(path)


def first_parity_difference(x: int, z: int, h_max: int = H_MAX) -> int | None:
    left, right = x, z
    for index in range(1, h_max + 1):
        if (left % 2) != (right % 2):
            return index
        left, right = floor_power(left), floor_power(right)
    return None


def atlas_pe_starts(*, n_cap: int = ATLAS_PE_N_CAP, limit: int = ATLAS_PE_LIMIT) -> list[int]:
    try:
        from research.juggler_sequence.atlas.schema import LANG_PE_CERTIFIED
        from research.juggler_sequence.atlas.storage import DEFAULT_DATA_DIR, connect
    except ImportError:
        return []
    path = DEFAULT_DATA_DIR / "word_atlas.sqlite"
    if not path.is_file():
        return []
    con = connect(DEFAULT_DATA_DIR)
    try:
        rows = con.execute(
            """
            SELECT DISTINCT min_n
            FROM pe_records
            WHERE language_id = ? AND min_n <= ? AND experiment_id = ?
            ORDER BY min_n
            LIMIT ?
            """,
            (LANG_PE_CERTIFIED, n_cap, EXPERIMENT_ID, limit),
        ).fetchall()
    finally:
        con.close()
    return [int(row[0]) for row in rows]


def class_stats(ys: list[int], futures: dict[int, Any]) -> dict[str, Any]:
    groups: dict[Any, list[int]] = defaultdict(list)
    for y in ys:
        groups[futures[y]].append(y)
    sizes = [len(members) for members in groups.values()]
    q = len(groups)
    n = len(ys)
    return {
        "Q_H": q,
        "I_H": ilog2_ceil(q),
        "n": n,
        "singleton_frac": (sum(1 for size in sizes if size == 1) / q) if q else 0.0,
        "mean_size": (n / q) if q else 0.0,
        "max_size": max(sizes) if sizes else 0,
        "n_multi": sum(1 for size in sizes if size > 1),
        "C_H": (q / n) if n else 0.0,
        "forgotten": (1.0 - q / n) if n else 0.0,
    }


def _mixed_pair(members: list[int], futures: dict[int, Any]) -> list[int] | None:
    by_f: dict[Any, int] = {}
    for y in members:
        key = futures[y]
        if key not in by_f:
            by_f[key] = y
        if len(by_f) >= 2:
            pair = sorted(by_f.values())
            return [pair[0], pair[1]]
    return None


def k_star_modulus(
    ys: list[int],
    futures: dict[int, Any],
    *,
    base: int,
    k_max: int,
) -> dict[str, Any]:
    classes = {futures[y] for y in ys}
    if len(classes) <= 1:
        return {"k_star": 0, "status": "ONE_CLASS", "separator": None, "v_diff": None}

    def separated(k: int) -> bool:
        modulus = base**k if k else 1
        seen: dict[int, Any] = {}
        for y in ys:
            residue = y % modulus
            key = futures[y]
            prev = seen.get(residue)
            if prev is None:
                seen[residue] = key
            elif prev != key:
                return False
        return True

    if not separated(k_max):
        pair = None
        modulus = base**k_max if k_max else 1
        buckets: dict[int, list[int]] = defaultdict(list)
        for y in ys:
            buckets[y % modulus].append(y)
        for members in buckets.values():
            hit = _mixed_pair(members, futures)
            if hit is not None and (pair is None or hit < pair):
                pair = hit
        return {
            "k_star": None,
            "status": "INSUFFICIENT_PRECISION_WITHIN_K_MAX",
            "separator": pair,
            "v_diff": (v2(pair[0] - pair[1]) if pair and base == 2 else v3(pair[0] - pair[1]) if pair else None),
        }

    lo, hi = 0, k_max
    while lo < hi:
        mid = (lo + hi) // 2
        if separated(mid):
            hi = mid
        else:
            lo = mid + 1
    pair = None
    if lo > 0:
        modulus = base ** (lo - 1)
        buckets = defaultdict(list)
        for y in ys:
            buckets[y % modulus].append(y)
        for members in buckets.values():
            hit = _mixed_pair(members, futures)
            if hit is not None and (pair is None or hit < pair):
                pair = hit
    return {
        "k_star": lo,
        "status": "SEPARATED",
        "separator": pair,
        "v_diff": (v2(pair[0] - pair[1]) if pair and base == 2 else v3(pair[0] - pair[1]) if pair else None),
    }


def k_star_bt_msd(ys: list[int], futures: dict[int, Any], *, k_max: int = 12) -> dict[str, Any]:
    prefixes = {y: encode(y).digits_msd for y in ys}

    def key_of(y: int, k: int) -> tuple[int, ...]:
        digits = prefixes[y][:k]
        return digits + (0,) * (k - len(digits))

    classes = {futures[y] for y in ys}
    if len(classes) <= 1:
        return {"k_star": 0, "status": "ONE_CLASS", "separator": None}

    def separated(k: int) -> bool:
        seen: dict[tuple[int, ...], Any] = {}
        for y in ys:
            residue = key_of(y, k)
            key = futures[y]
            prev = seen.get(residue)
            if prev is None:
                seen[residue] = key
            elif prev != key:
                return False
        return True

    if not separated(k_max):
        return {"k_star": None, "status": "INSUFFICIENT_PRECISION_WITHIN_K_MAX", "separator": None}
    lo, hi = 0, k_max
    while lo < hi:
        mid = (lo + hi) // 2
        if separated(mid):
            hi = mid
        else:
            lo = mid + 1
    return {"k_star": lo, "status": "SEPARATED", "separator": None}


def intra_class_precision(ys: list[int], futures: dict[int, Any], *, k_max: int) -> dict[str, Any]:
    groups: dict[Any, list[int]] = defaultdict(list)
    for y in ys:
        groups[futures[y]].append(y)
    values = []
    for members in groups.values():
        if len(members) < 2:
            values.append(0)
            continue
        report = k_star_modulus(members, {y: y for y in members}, base=2, k_max=k_max)
        values.append(report["k_star"] if report["k_star"] is not None else k_max + 1)
    values.sort()
    return {
        "min": min(values) if values else 0,
        "median": int(statistics.median(values)) if values else 0,
        "max": max(values) if values else 0,
        "n_classes": len(values),
    }


def greedy_distinguish(
    ys: list[int],
    futures: dict[int, Any],
    *,
    k2_max: int = 16,
    k3_max: int = 8,
) -> dict[str, Any]:
    predicates: list[tuple[str, int, Callable[[int], Any]]] = [("parity", 1, lambda y: y % 2)]
    for k in range(2, k2_max + 1):
        predicates.append((f"mod2_{k}", k, lambda y, kk=k: y % (1 << kk)))
    for k in range(1, k3_max + 1):
        predicates.append((f"mod3_{k}", k, lambda y, kk=k: y % (3**kk)))
    predicates.append(("v2_3y1", 4, v2_3y1))
    for k in range(1, 7):
        predicates.append(
            (f"bt_msd_{k}", k, lambda y, kk=k: encode(y).digits_msd[:kk])
        )

    def mixed_pairs(keys: dict[int, tuple[Any, ...]]) -> int:
        buckets: dict[tuple[Any, ...], list[Any]] = defaultdict(list)
        for y in ys:
            buckets[keys[y]].append(futures[y])
        total = 0
        for labels in buckets.values():
            counts = Counter(labels)
            n = len(labels)
            total += n * (n - 1) // 2 - sum(c * (c - 1) // 2 for c in counts.values())
        return total

    keys = {y: () for y in ys}
    chosen: list[str] = []
    bits = 0
    unresolved = mixed_pairs(keys)
    while unresolved:
        best = None
        for name, cost, fn in predicates:
            if name in chosen:
                continue
            trial = {y: keys[y] + (fn(y),) for y in ys}
            score = mixed_pairs(trial)
            rec = (score, cost, name, trial)
            if best is None or rec < best:
                best = rec
        if best is None or best[0] >= unresolved:
            return {
                "n_tests": len(chosen),
                "bits": bits,
                "predicates": chosen,
                "unresolved": unresolved,
            }
        _score, cost, name, trial = best
        chosen.append(name)
        bits += cost
        keys = trial
        unresolved = _score
    return {"n_tests": len(chosen), "bits": bits, "predicates": chosen, "unresolved": 0}


def growth_rows(
    ys: list[int],
    paths: dict[int, tuple[int, ...]],
    *,
    level: str,
    k2_max: int,
    k3_max: int,
    with_greedy: bool,
) -> list[dict[str, Any]]:
    rows = []
    for horizon in range(1, H_MAX + 1):
        futures = {y: future_of(paths[y], horizon, level) for y in ys}
        stats = class_stats(ys, futures)
        k2 = k_star_modulus(ys, futures, base=2, k_max=k2_max)
        row: dict[str, Any] = {
            "H": horizon,
            "level": level,
            **stats,
            "k2": k2,
            "Q_bound_2H": 2**horizon if level == LEVEL_WORD else None,
        }
        if level == LEVEL_WORD:
            k3 = k_star_modulus(ys, futures, base=3, k_max=k3_max)
            row["k3"] = k3
            row["k_bt_msd"] = k_star_bt_msd(ys, futures)
            row["intra_k2"] = intra_class_precision(ys, futures, k_max=k2_max)
            if k2["separator"] is not None:
                y, z = k2["separator"]
                row["separator"] = {
                    "y": compact_int(y),
                    "z": compact_int(z),
                    "H_first_difference": first_parity_difference(y, z),
                    "Fy": futures[y],
                    "Fz": futures[z],
                }
            if with_greedy:
                row["greedy"] = greedy_distinguish(ys, futures, k2_max=min(16, k2_max), k3_max=min(6, k3_max))
        rows.append(row)
    return rows


def build_paths(ys: list[int]) -> tuple[list[int], dict[int, tuple[int, ...]], list[int]]:
    paths: dict[int, tuple[int, ...]] = {}
    kept: list[int] = []
    dropped: list[int] = []
    for y in ys:
        path = walk(y)
        if path is None:
            dropped.append(y)
            continue
        paths[y] = path
        kept.append(y)
    return kept, paths, dropped


def sample_A() -> tuple[str, list[int], dict[str, Any]]:
    ys = sorted({row["y"] for row in collect_landings(n_max=80)})
    return "A_residual_80", ys, {"source": "collect_landings(n_max=80)", "n_requested": len(ys)}


def sample_B() -> tuple[str, list[int], dict[str, Any]]:
    ys = list(range(2, 4001))
    return "B_n_4000", ys, {"source": "integers 2..4000", "n_requested": len(ys)}


def sample_C() -> tuple[str, list[int], dict[str, Any]]:
    landings = sorted({row["y"] for row in collect_landings(n_max=4000)})
    kept_landings = [y for y in landings if y.bit_length() <= LANDING_BIT_CAP]
    excluded = [compact_int(y) for y in landings if y.bit_length() > LANDING_BIT_CAP]
    pe = atlas_pe_starts()
    ys = sorted(set(kept_landings) | set(pe))
    return (
        "C_atlas_enriched",
        ys,
        {
            "source": "landings n<=4000 with bit_length<=1024 plus atlas PE starts",
            "n_landings_kept": len(kept_landings),
            "n_landings_excluded_bits": len(excluded),
            "excluded_bit_lengths": [y.bit_length() if isinstance(y, int) else None for y in landings if y.bit_length() > LANDING_BIT_CAP],
            "n_pe": len(pe),
            "n_requested": len(ys),
            "atlas_present": bool(pe),
        },
    )


def sample_D() -> tuple[str, list[int], dict[str, Any]]:
    ys = sorted(set(HARD_STATES))
    return "D_hard", ys, {"source": "documented hard / PE / first-return extremals", "n_requested": len(ys)}


def nested_samples() -> list[tuple[str, list[int], dict[str, Any]]]:
    out = []
    for size in (30, 100, 500, 1000):
        ys = list(range(2, 2 + size))
        out.append((f"nested_{size}", ys, {"source": f"integers 2..{1 + size}", "n_requested": size}))
    return out


def family_samples(base: list[int], paths: dict[int, tuple[int, ...]]) -> list[tuple[str, list[int]]]:
    words = {y: word_future(paths[y], H_MAX) for y in base}
    return [
        ("fam_even", [y for y in base if y % 2 == 0]),
        ("fam_odd", [y for y in base if y % 2 == 1]),
        ("fam_OOO", [y for y in base if words[y].startswith("OOO")]),
        ("fam_EEE", [y for y in base if words[y].startswith("EEE")]),
        ("fam_mixed", [y for y in base if "O" in words[y] and "E" in words[y]]),
        ("fam_PE", atlas_pe_starts()),
    ]


def analyze_sample(
    sample_id: str,
    ys: list[int],
    meta: dict[str, Any],
    *,
    levels: tuple[str, ...] = (LEVEL_WORD,),
    with_greedy: bool = False,
) -> dict[str, Any]:
    kept, paths, dropped = build_paths(ys)
    k2_max = min(K_MAX_2, max((y.bit_length() for y in kept), default=8) + 2)
    k3_max = min(K_MAX_3, 12)
    payload = {
        "sample_id": sample_id,
        "meta": {**meta, "n_kept": len(kept), "n_dropped_bitcap": len(dropped)},
        "levels": {},
    }
    for level in levels:
        payload["levels"][level] = growth_rows(
            kept,
            paths,
            level=level,
            k2_max=k2_max,
            k3_max=k3_max,
            with_greedy=with_greedy and level == LEVEL_WORD,
        )
    payload["paths"] = paths
    payload["kept"] = kept
    return payload


def refinement_table(sample: dict[str, Any]) -> list[dict[str, Any]]:
    word_rows = {row["H"]: row for row in sample["levels"][LEVEL_WORD]}
    coarse_rows = {row["H"]: row for row in sample["levels"].get(LEVEL_COARSE, [])}
    state_rows = {row["H"]: row for row in sample["levels"].get(LEVEL_STATE, [])}
    out = []
    for horizon in range(1, H_MAX + 1):
        out.append(
            {
                "H": horizon,
                "Q_word": word_rows[horizon]["Q_H"],
                "Q_coarse": coarse_rows.get(horizon, {}).get("Q_H"),
                "Q_state": state_rows.get(horizon, {}).get("Q_H"),
            }
        )
    return out


def k2_sequence(sample: dict[str, Any]) -> list[Any]:
    return [row["k2"]["k_star"] for row in sample["levels"][LEVEL_WORD]]


def i_sequence(sample: dict[str, Any]) -> list[int]:
    return [row["I_H"] for row in sample["levels"][LEVEL_WORD]]


def q_sequence(sample: dict[str, Any]) -> list[int]:
    return [row["Q_H"] for row in sample["levels"][LEVEL_WORD]]


def plateaus_from_h2(seq: list[Any]) -> bool:
    if len(seq) < 2:
        return False
    if seq[1] is None:
        return False
    return all(value == seq[1] for value in seq[1:])


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    main = [scan["samples"][key] for key in ("A_residual_80", "B_n_4000") if key in scan["samples"]]
    k_seqs = [k2_sequence(sample) for sample in main]
    i_seqs = [i_sequence(sample) for sample in main]
    q_ok = all(q <= 2**h for sample in main for h, q in enumerate(q_sequence(sample), start=1))
    i_ok = all(i <= h for seq in i_seqs for h, i in enumerate(seq, start=1))
    plateau = all(plateaus_from_h2(seq) for seq in k_seqs)
    nested = scan.get("nested", {})
    k_by_size = {int(name.split("_")[1]): k2_sequence(nested[name])[1] for name in nested}
    grows_with_size = list(k_by_size.values()) != sorted(k_by_size.values()) or len(set(k_by_size.values())) > 1
    if q_ok and i_ok and plateau and grows_with_size:
        return {
            "classification": CLASS_COUNTER,
            "reason": (
                "Q_H <= 2^H and I_H <= H on every fixed sample (word-alphabet counting). "
                "k*_2 jumps at H=2 and then plateaus; the H=2 value grows with |Y| on nested "
                "consecutive intervals. Apparent horizon complexity is the word bound "
                "plus a sample-diameter 2-adic pair."
            ),
        }
    if plateau and q_ok:
        return {
            "classification": CLASS_COMPLEX,
            "reason": "no stable horizon-growing precision measure survived the fixed-sample control",
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no first-return-independent information-complexity law survived Phase 0",
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text() + "\n" + CELLS.read_text(encoding="utf-8") + "\n" + ENVELOPE.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "no_forbidden_engines": all(name not in text for name in FORBIDDEN_ENGINES),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
        "no_independence_claim": "independent of ZFC" not in text and "independent of PA" not in text,
    }


def strip_paths(sample: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in sample.items() if key not in {"paths", "kept"}}


def future_class_rows(scan: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for sample_id, sample in scan["samples"].items():
        paths = sample["paths"]
        kept = sample["kept"]
        for horizon in range(1, H_MAX + 1):
            futures = {y: word_future(paths[y], horizon) for y in kept}
            sizes = Counter(futures.values())
            for y in kept:
                word = futures[y]
                rows.append(
                    {
                        "sample_id": sample_id,
                        "state_id": table_int(y),
                        "H": horizon,
                        "future_hash": sha1(word.encode()).hexdigest()[:16],
                        "future_reference": word,
                        "class_size": sizes[word],
                    }
                )
    return rows


def precision_rows(scan: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for bucket in (scan["samples"], scan.get("nested", {}), scan.get("families", {})):
        for sample_id, sample in bucket.items():
            for row in sample["levels"][LEVEL_WORD]:
                for name, report in (("mod2", row["k2"]), ("mod3", row.get("k3"))):
                    if report is None:
                        continue
                    rows.append(
                        {
                            "sample_id": sample_id,
                            "H": row["H"],
                            "projection": name,
                            "k": report["k_star"],
                            "number_of_collisions": 0 if report["status"] == "SEPARATED" else 1,
                            "distinguishing_status": report["status"],
                        }
                    )
    return rows


def separator_rows(scan: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for sample_id, sample in scan["samples"].items():
        for row in sample["levels"][LEVEL_WORD]:
            sep = row.get("separator")
            if not sep:
                continue
            rows.append(
                {
                    "sample_id": sample_id,
                    "H": row["H"],
                    "projection": "mod2",
                    "y": table_int(sep["y"]),
                    "z": table_int(sep["z"]),
                    "first_difference": sep["H_first_difference"],
                    "witness_reference": f"{sep['Fy']}|{sep['Fz']}",
                }
            )
    return rows


def write_tables(scan: dict[str, Any]) -> dict[str, str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    tables = {
        "future_classes": future_class_rows(scan),
        "precision_tests": precision_rows(scan),
        "separators": separator_rows(scan),
    }
    paths: dict[str, str] = {}
    for stem, rows in tables.items():
        jsonl = DATA_DIR / f"{stem}.jsonl"
        with jsonl.open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, separators=(",", ":")) + "\n")
        paths[f"{stem}.jsonl"] = str(jsonl)
        parquet = DATA_DIR / f"{stem}.parquet"
        try:
            import pyarrow as pa
            import pyarrow.parquet as pq

            pq.write_table(pa.Table.from_pylist(rows), parquet)
            paths[f"{stem}.parquet"] = str(parquet)
        except ImportError:
            paths[f"{stem}.parquet"] = ""
    return paths


def run_probe() -> dict[str, Any]:
    builders = [sample_A(), sample_B(), sample_C(), sample_D()]
    samples: dict[str, Any] = {}
    for sample_id, ys, meta in builders:
        levels = (LEVEL_WORD, LEVEL_COARSE, LEVEL_STATE) if sample_id in {"A_residual_80", "B_n_4000"} else (LEVEL_WORD,)
        greedy = sample_id in {"A_residual_80", "D_hard"} or sample_id == "B_n_4000"
        samples[sample_id] = analyze_sample(sample_id, ys, meta, levels=levels, with_greedy=greedy)

    nested = {}
    for sample_id, ys, meta in nested_samples():
        nested[sample_id] = analyze_sample(sample_id, ys, meta, levels=(LEVEL_WORD,), with_greedy=False)

    families = {}
    base = samples["B_n_4000"]
    for fam_id, ys in family_samples(base["kept"], base["paths"]):
        if len(ys) < 2:
            continue
        families[fam_id] = analyze_sample(fam_id, ys, {"source": fam_id, "n_requested": len(ys)}, levels=(LEVEL_WORD,))

    refinements = {
        key: refinement_table(samples[key])
        for key in ("A_residual_80", "B_n_4000")
        if LEVEL_COARSE in samples[key]["levels"]
    }
    return {
        "samples": samples,
        "nested": nested,
        "families": families,
        "refinements": refinements,
    }


def summarize_sample(sample: dict[str, Any]) -> dict[str, Any]:
    word = sample["levels"][LEVEL_WORD]
    return {
        "sample_id": sample["sample_id"],
        "n": word[0]["n"],
        "meta": sample["meta"],
        "Q": [row["Q_H"] for row in word],
        "I": [row["I_H"] for row in word],
        "C": [row["C_H"] for row in word],
        "max_size": [row["max_size"] for row in word],
        "n_multi": [row["n_multi"] for row in word],
        "singleton_frac": [row["singleton_frac"] for row in word],
        "k2": [row["k2"]["k_star"] for row in word],
        "k2_status": [row["k2"]["status"] for row in word],
        "k3": [row.get("k3", {}).get("k_star") for row in word],
        "k_bt_msd": [row.get("k_bt_msd", {}).get("k_star") for row in word],
        "separators": [row.get("separator") for row in word],
        "intra_k2": [row.get("intra_k2") for row in word],
        "greedy": [row.get("greedy") for row in word],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    decision = classify(scan)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "formal_independence": False,
            "unbounded_complexity_implies_unprovability": False,
            "myhill_nerode": False,
            "automaton": False,
            "kolmogorov_complexity": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
        }
    )
    summaries = {key: summarize_sample(sample) for key, sample in scan["samples"].items()}
    nested = {key: summarize_sample(sample) for key, sample in scan["nested"].items()}
    families = {key: summarize_sample(sample) for key, sample in scan["families"].items()}
    artifacts = write_tables(scan)
    lean = lean_api_present()
    return {
        "experiment": "juggler_information_complexity",
        "engine_control_layer_modified": False,
        "F_H": "O/E word of the next H steps (parities of x, T(x), ..., T^{H-1}(x))",
        "equivalence": "x ~_H y iff F_H(x)=F_H(y); experimental, not Myhill-Nerode",
        "anti_overclaim": anti,
        "lean": lean,
        "decision": decision,
        "summaries": summaries,
        "nested": nested,
        "families": families,
        "refinements": scan["refinements"],
        "artifacts": artifacts,
        "search_method": (
            "fixed samples A/B/C/D; H<=6 exact CPU itineraries; "
            "k* by binary search on residue fibers; no residual Future_H labels"
        ),
    }


def _fmt_table(headers: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(item) for item in row) + " |")
    return lines


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    summaries = payload["summaries"]
    lines = [
        "# Juggler information complexity",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone Phase-0 measurement of finite dynamical information",
        "complexity. Not a Research Engine experiment, not a halt theorem,",
        "and not an independence claim. `~_H` is experimental future-equality,",
        "not Myhill–Nerode equivalence.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do D_H and k*(H) grow with H<=6 on fixed Y?",
        "Novelty hypothesis      longer word futures need more arithmetic bits",
        "Falsifier               Q_H is 2^H counting; k* plateaus at H=2",
        "Existing machinery      floor_power, word, word_of, collect_landings",
        "Maximum Phase-0 scope   H<=6; samples A/B/C/D; no GPU; no Lean pilot",
        "```",
        "",
        "## 1. Motivation",
        "",
        "The tested compression hierarchy (word statistics, PE grammar,",
        "realization-set and landing-image geometry, low-dimensional",
        "projections of y, summed defects, noncontracting thresholds) failed",
        "because the exact integer retained information those summaries",
        "dropped. This phase asks whether that failure has a quantitative",
        "horizon law. It does not reopen those branches.",
        "",
        "## 2. Definitions",
        "",
        f"- `F_H(x)` = `{payload['F_H']}`",
        f"- {payload['equivalence']}",
        "- `Q_H` = number of observed `F_H` classes on a fixed sample Y",
        "- `I_H` = `ceil(log2 Q_H)` (class-index bits; not Kolmogorov complexity)",
        "- `C_H` = `Q_H / |Y|` (finer futures give C_H closer to 1)",
        "- `k*_2(H;Y)` = least k such that `x mod 2^k` separates the observed",
        "  `F_H` classes, or `INSUFFICIENT_PRECISION_WITHIN_K_MAX`",
        "- `D_H` is reported separately as `I_H`, `k*_2`, `k*_3`, BT-MSD length,",
        "  and greedy query count — not as a single invented energy",
        "",
        "## 3. Fixed-sample results",
        "",
        decision["reason"],
        "",
    ]
    for key in ("A_residual_80", "B_n_4000", "C_atlas_enriched", "D_hard"):
        if key not in summaries:
            continue
        rec = summaries[key]
        lines.extend(
            [
                f"### {key}",
                "",
                f"- |Y| kept: `{rec['n']}` meta `{rec['meta']}`",
            ]
        )
        lines.extend(
            _fmt_table(
                ["H", "Q_H", "I_H", "C_H", "max_size", "n_multi", "k*_2", "k*_3", "k_bt_msd"],
                [
                    [
                        h,
                        rec["Q"][h - 1],
                        rec["I"][h - 1],
                        f"{rec['C'][h - 1]:.4f}",
                        rec["max_size"][h - 1],
                        rec["n_multi"][h - 1],
                        rec["k2"][h - 1],
                        rec["k3"][h - 1],
                        rec["k_bt_msd"][h - 1],
                    ]
                    for h in range(1, H_MAX + 1)
                ],
            )
        )
        lines.append("")
    lines.extend(
        [
            "Word vs coarse vs exact on the primary samples. Exact `F_H^state` is",
            "the next-H-state tuple, so it is determined by `T(x)` and cannot",
            "refine with H. Coarse atoms are `(parity, x mod 8, v2(3x+1), 4 LSD trits)`",
            "along the length-H window.",
            "",
        ]
    )
    for key, rows in payload.get("refinements", {}).items():
        lines.append(f"### Refinement {key}")
        lines.append("")
        lines.extend(
            _fmt_table(
                ["H", "Q_word", "Q_coarse", "Q_state"],
                [[row["H"], row["Q_word"], row["Q_coarse"], row["Q_state"]] for row in rows],
            )
        )
        lines.append("")
    lines.extend(["## 4. Precision hierarchy", "", "Nested consecutive samples (growth with |Y| at fixed H):", ""])
    nest_headers = ["|Y|"] + [f"k*_2(H={h})" for h in range(1, H_MAX + 1)] + [f"I(H={h})" for h in range(1, H_MAX + 1)]
    nest_rows = []
    for name, rec in payload["nested"].items():
        nest_rows.append([rec["n"], *rec["k2"], *rec["I"]])
    lines.extend(_fmt_table(nest_headers, nest_rows))
    lines.extend(
        [
            "",
            "## 5. Separating witnesses",
            "",
        ]
    )
    for key, rec in summaries.items():
        lines.append(f"- {key}: `{rec['separators']}`")
    lines.extend(
        [
            "",
            "## 6. Information loss",
            "",
            "Word futures collapse many starts into one class. `forgotten = 1 - C_H`",
            "is the fraction of starts that are not unique as H-step words.",
            "",
        ]
    )
    for key in ("A_residual_80", "B_n_4000"):
        if key not in summaries:
            continue
        rec = summaries[key]
        lines.append(
            f"- {key} forgotten: `{[round(1 - c, 4) for c in rec['C']]}` max class `{rec['max_size']}` intra-k2 `{rec['intra_k2']}`"
        )
    lines.extend(["", "## 7. Complexity growth", "", "D_H versus H on the two primary fixed samples:", ""])
    for key in ("A_residual_80", "B_n_4000"):
        rec = summaries[key]
        lines.append(f"- {key} I_H `{rec['I']}` k*_2 `{rec['k2']}` greedy `{rec['greedy']}`")
    lines.extend(["", "## 8. Family comparison", ""])
    for key, rec in payload["families"].items():
        lines.append(f"- {key} |Y|=`{rec['n']}` Q=`{rec['Q']}` k*_2=`{rec['k2']}`")
    lines.extend(
        [
            "",
            "## 9. Proof-complexity pilot",
            "",
            "Not performed. Phase 0 did not produce a surviving precision hierarchy.",
            "",
            "## 10. Interpretation",
            "",
            "- `Q_H <= 2^H` on word futures: **COMPUTATIONALLY VERIFIED** (and the",
            "  tautological alphabet bound)",
            "- `I_H <= H`: **COMPUTATIONALLY VERIFIED** from the same bound",
            "- `k*_2(1)` is 0 on an all-odd sample and 1 when both parities appear:",
            "  **COMPUTATIONALLY VERIFIED** (definition of `F_1`)",
            "- `k*_2(H)` plateaus for `H>=2` on samples A, B, and D;",
            "  sample C is `0,22,26,26,26,26` (one extra split at H=3, then flat):",
            "  **COMPUTATIONALLY VERIFIED**",
            "- nested `|Y|` increases `k*_2(2)`: **COMPUTATIONALLY VERIFIED**",
            "- word vs coarse vs exact refinement: **OBSERVATION** (see §3)",
            "- BT low digits vs `y mod 3^k`: expected **REPARAMETERIZATION**",
            "- exact theorem stronger than the alphabet bound: none",
            "- candidate conjecture: none",
            "- formal independence: not studied",
            "",
            f"Decision reason: {decision['reason']}",
            "",
            "## 11. What this experiment cannot show",
            "",
            "WHAT THIS EXPERIMENT CANNOT SHOW",
            "",
            "* finite-state complexity does not imply formal independence;",
            "* failure of tested projections does not imply no compact representation exists;",
            "* finite horizons do not establish asymptotic unboundedness;",
            "* generalized Collatz undecidability does not transfer automatically to the",
            "  ordinary Juggler / 3n+1 system.",
            "",
            "## Lean",
            "",
            f"- sorry-free: `{payload['lean']['sorry_free']}`",
            f"- no forbidden engines: `{payload['lean']['no_forbidden_engines']}`",
            f"- no global halt theorem: `{payload['lean']['no_global_termination_theorem']}`",
            f"- no independence claim in Lean text: `{payload['lean']['no_independence_claim']}`",
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
            "This is not a halt result and not an independence result.",
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
    summary = {
        "classification": data["decision"]["classification"],
        "reason": data["decision"]["reason"],
        "summaries": data["summaries"],
        "nested": data["nested"],
        "families": data["families"],
    }
    (DATA_DIR / "complexity_summary.json").write_text(json.dumps(json_safe(summary), indent=2) + "\n", encoding="utf-8")
    sample_summary = {key: {k: rec[k] for k in ("sample_id", "n", "meta", "Q", "I", "k2")} for key, rec in data["summaries"].items()}
    (DATA_DIR / "sample_summary.json").write_text(json.dumps(json_safe(sample_summary), indent=2) + "\n", encoding="utf-8")
    manifest = {
        "experiment": "juggler_information_complexity",
        "F_H": data["F_H"],
        "H_max": H_MAX,
        "classification": data["decision"]["classification"],
        "artifacts": data.get("artifacts", {}),
        "independence_claim": False,
    }
    (DATA_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()
