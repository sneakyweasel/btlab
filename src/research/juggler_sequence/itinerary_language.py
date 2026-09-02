"""Juggler word languages. Not a termination theorem.

Existential languages: an word is in L if some n realises it, in L_up
if some realisation expands, and in the PE languages if it is a
persistent-expanding residual block or a concatenation of such blocks.
The census compares realised factor/prefix/suffix sets to the known
O^a E^b grammar. Isolated-odd factors such as EOE are that grammar,
not a new arrangement law.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
from typing import Any

from research.juggler_sequence.compensated_contraction import (
    follows_itinerary,
    image_after,
)
from research.juggler_sequence.expanding_grammar import (
    classify_exit,
    max_expanding_evens,
)
from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.expansion_slack import walk_pe_run
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.normalized_defect import odd_even_word
from research.juggler_sequence.power_itineraries import itinerary, word_of
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    exponent_expanding,
    odd_odd_starts,
    sequel_of,
)

N_MAX = 2000
CHAIN_CAP = 24
FACT_R_MAX = 6
GRAMMAR_A_MAX = 12
GRAMMAR_BLOCKS = 3
L_R_MAX = 8

LEAN_THEOREMS = (
    "jugglerLanguage",
    "expandingLanguage",
    "persistentExpandingLanguage",
    "itineraryPrefix",
    "itinerarySuffix",
    "itineraryFactor",
    "jugglerLanguage_of_follows",
    "jugglerLanguage_prefix",
    "jugglerLanguage_suffix",
    "jugglerLanguage_factor",
    "ooe_mem_expandingLanguage",
    "oe_not_mem_expandingLanguage",
    "oe_factor_of_ooe",
    "expandingLanguage_not_factor_closed",
    "ooe_mem_persistentExpandingLanguage",
)

EXAMPLES = {
    "ooe": "OOE",
    "oe": "OE",
    "eoe": "EOE",
    "eeoe": "EEOE",
    "ooe_start": 5,
    "eeoe_start": 2500,
    "pe_run_365": "OOEOOEOOE",
}

# Grammar-legal PE factors missing at n≤8000 that appear on known
# longer runs. Not a surviving forbidden-factor law.
LATE_PE_FACTORS = {
    "OEEEEO": {"start": 9157, "words": ("OOOOOOOOEEEE", "OOE")},
    "EEEEEE": {
        "start": 14237,
        "words": (
            "OOOOOEE",
            "OOE",
            "OOOOOOOOOOOEEEEEE",
            "OOE",
            "OOE",
            "OOOE",
            "OOOOOEE",
        ),
    },
}

KNOWN_GRAMMAR_FORBIDDEN = ("EOE",)


def all_binary_words(r: int) -> list[str]:
    if r < 0:
        raise ValueError("r must be nonnegative")
    return [
        "".join("O" if (mask >> i) & 1 else "E" for i in range(r))
        for mask in range(1 << r)
    ]


def factors(word: str, r: int) -> set[str]:
    if r <= 0 or r > len(word):
        return set()
    return {word[i : i + r] for i in range(len(word) - r + 1)}


def prefixes(word: str, r: int) -> set[str]:
    if r <= 0 or r > len(word):
        return set()
    return {word[:r]}


def suffixes(word: str, r: int) -> set[str]:
    if r <= 0 or r > len(word):
        return set()
    return {word[-r:]}


def contains_isolated_odd(word: str) -> bool:
    return "EOE" in word


def legal_pe_blocks(*, a_max: int = GRAMMAR_A_MAX) -> list[tuple[int, int]]:
    blocks: list[tuple[int, int]] = []
    for a in range(2, a_max + 1):
        for b in range(1, max_expanding_evens(a) + 1):
            if exponent_expanding(a, b):
                blocks.append((a, b))
    return blocks


def grammar_concatenations(
    *, a_max: int = GRAMMAR_A_MAX, block_cap: int = GRAMMAR_BLOCKS
) -> list[str]:
    blocks = [odd_even_word(a, b) for a, b in legal_pe_blocks(a_max=a_max)]
    words: list[str] = []
    for length in range(1, block_cap + 1):
        for parts in product(blocks, repeat=length):
            words.append("".join(parts))
    return words


def collect_slices(words: list[str], r_max: int) -> dict[str, dict[int, set[str]]]:
    out: dict[str, dict[int, set[str]]] = {
        "fact": {r: set() for r in range(1, r_max + 1)},
        "pref": {r: set() for r in range(1, r_max + 1)},
        "suff": {r: set() for r in range(1, r_max + 1)},
    }
    for word in words:
        for r in range(1, r_max + 1):
            out["fact"][r] |= factors(word, r)
            out["pref"][r] |= prefixes(word, r)
            out["suff"][r] |= suffixes(word, r)
    return out


def even_parents(m: int) -> list[int]:
    lo, hi = even_preimage(m)
    return [n for n in range(lo, hi) if n % 2 == 0]


def odd_parents(m: int) -> list[int]:
    return [n for n in odd_preimage_integers(m) if n % 2 == 1]


def pullback_realizers(
    word: str, images: range, *, cap: int = 64
) -> list[int]:
    """Starts that realise ``word`` and land in ``images``. Empty over a
    bounded image interval is not unrealisability. The parent set is
    capped so long even pullbacks stay cheap.
    """

    states = sorted(n for n in images if n >= 1)[:cap]
    for letter in reversed(word):
        nxt: list[int] = []
        parent = even_parents if letter == "E" else odd_parents
        for m in states:
            nxt.extend(parent(m))
            if len(nxt) >= cap:
                break
        states = sorted(set(nxt))[:cap]
        if not states:
            return []
    return [n for n in states if n >= 1]


def language_completeness(
    *, r_max: int = L_R_MAX, n_max: int = N_MAX, pullback_image: int = 64
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for r in range(1, r_max + 1):
        universe = set(all_binary_words(r))
        first: dict[str, int] = {}
        first_up: dict[str, int] = {}
        for n in range(1, n_max + 1):
            path = itinerary(n, r)
            word = word_of(path)
            if word not in first:
                first[word] = n
            if path[-1] > n and word not in first_up:
                first_up[word] = n
        missing = sorted(universe - set(first))
        pulled: dict[str, int] = {}
        still_missing: list[str] = []
        if missing and r <= 6:
            images = range(1, pullback_image + 1)
            for word in missing:
                starts = pullback_realizers(word, images)
                if starts:
                    pulled[word] = starts[0]
                    first[word] = starts[0]
                else:
                    still_missing.append(word)
        else:
            still_missing = missing
        missing_up = sorted(set(first) - set(first_up))
        rows.append(
            {
                "r": r,
                "universe": len(universe),
                "realized": len(first),
                "expanding": len(first_up),
                "missing_forward": missing,
                "pulled": pulled,
                "missing": still_missing,
                "realized_not_expanding": missing_up[:20],
                "realized_not_expanding_count": len(missing_up),
                "full": not still_missing,
            }
        )
    return {"n_max": n_max, "pullback_image": pullback_image, "rows": rows}


def pe_run_word(run: list[dict[str, Any]]) -> str:
    return "".join(row["word"] for row in run)


def realized_pe_runs(
    *, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP
) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    seen: set[int] = set()
    queue = list(starts)
    run_words: list[str] = []
    block_words: list[str] = []
    landings: list[int] = []
    prefix_futures: dict[str, set[str]] = defaultdict(set)
    landing_futures: dict[int, str] = {}
    exits: Counter[str] = Counter()
    terminal_suffixes: dict[str, Counter[str]] = {
        "leave_odd_odd": Counter(),
        "descent": Counter(),
        "other": Counter(),
        "none": Counter(),
    }
    max_run = 0
    max_run_start = None
    while queue:
        x = queue.pop()
        if x in seen or x <= 1:
            continue
        seen.add(x)
        run = walk_pe_run(x, cap=chain_cap)
        if not run:
            continue
        word = pe_run_word(run)
        run_words.append(word)
        if len(run) > max_run:
            max_run = len(run)
            max_run_start = run[0]["x"]
        prefix = ""
        for i, row in enumerate(run):
            block_words.append(row["word"])
            landings.append(row["x"])
            nxt = run[i + 1]["word"] if i + 1 < len(run) else "END"
            prefix_futures[prefix].add(nxt)
            landing_futures[row["x"]] = nxt
            prefix += row["word"]
        prefix_futures[prefix].add("END")
        last = run[-1]
        seq = sequel_of(last["y"])
        kind = classify_exit(seq)
        exits[kind] += 1
        tail = last["word"] if len(last["word"]) <= FACT_R_MAX else last["word"][-FACT_R_MAX:]
        terminal_suffixes.setdefault(kind, Counter())[tail] += 1
        if (
            seq is not None
            and seq["y"] not in seen
            and seq["y"] > n_max
            and seq["y"] % 2 == 1
        ):
            raw = residual_excursion(seq["y"])
            if raw is not None:
                nxt = classify_step(seq["y"], raw)
                if nxt["persistent"] and nxt["expanding"]:
                    queue.append(seq["y"])
    return {
        "n_max": n_max,
        "visited": len(seen),
        "run_words": run_words,
        "block_words": block_words,
        "landings": landings,
        "prefix_futures": {k: sorted(v) for k, v in prefix_futures.items()},
        "landing_futures": landing_futures,
        "exits": dict(exits),
        "terminal_suffixes": {
            kind: dict(counter) for kind, counter in terminal_suffixes.items()
        },
        "max_run": max_run,
        "max_run_start": max_run_start,
    }


def _sorted_sets(slices: dict[str, dict[int, set[str]]]) -> dict[str, dict[int, list[str]]]:
    return {
        kind: {r: sorted(vals) for r, vals in rows.items()}
        for kind, rows in slices.items()
    }


def factor_comparison(
    realized_words: list[str],
    *,
    r_max: int = FACT_R_MAX,
    a_max: int = GRAMMAR_A_MAX,
    block_cap: int = GRAMMAR_BLOCKS,
) -> dict[str, Any]:
    grammar_words = grammar_concatenations(a_max=a_max, block_cap=block_cap)
    grammar = collect_slices(grammar_words, r_max)
    realized = collect_slices(realized_words, r_max)
    missing: dict[str, dict[int, list[str]]] = {}
    extra: dict[str, dict[int, list[str]]] = {}
    isolated = 0
    for kind in ("fact", "pref", "suff"):
        missing[kind] = {}
        extra[kind] = {}
        for r in range(1, r_max + 1):
            miss = grammar[kind][r] - realized[kind][r]
            surplus = realized[kind][r] - grammar[kind][r]
            missing[kind][r] = sorted(miss)
            extra[kind][r] = sorted(surplus)
            isolated += sum(1 for word in miss if contains_isolated_odd(word))
    return {
        "grammar_counts": {
            kind: {r: len(vals) for r, vals in rows.items()}
            for kind, rows in grammar.items()
        },
        "realized_counts": {
            kind: {r: len(vals) for r, vals in rows.items()}
            for kind, rows in realized.items()
        },
        "grammar": _sorted_sets(grammar),
        "realized": _sorted_sets(realized),
        "missing": missing,
        "extra": extra,
        "missing_isolated_odd": isolated,
        "fills_grammar_factors": all(not missing["fact"][r] for r in range(1, r_max + 1)),
        "fills_grammar_prefs": all(not missing["pref"][r] for r in range(1, r_max + 1)),
        "fills_grammar_suffs": all(not missing["suff"][r] for r in range(1, r_max + 1)),
    }


def myhill_nerode_proxy(pe: dict[str, Any]) -> dict[str, Any]:
    prefix_futures: dict[str, list[str]] = pe["prefix_futures"]
    landing_futures: dict[int, str] = pe["landing_futures"]
    future_to_prefixes: dict[tuple[str, ...], list[str]] = defaultdict(list)
    for prefix, futures in prefix_futures.items():
        future_to_prefixes[tuple(futures)].append(prefix)
    future_to_landings: dict[str, list[int]] = defaultdict(list)
    for landing, nxt in landing_futures.items():
        future_to_landings[nxt].append(landing)
    split_prefixes = [p for p, futures in prefix_futures.items() if len(futures) > 1]
    return {
        "n_prefixes": len(prefix_futures),
        "n_prefix_classes": len(future_to_prefixes),
        "n_landings": len(landing_futures),
        "n_landing_classes": len(future_to_landings),
        "split_prefixes": sorted(split_prefixes, key=len),
        "split_prefix_count": len(split_prefixes),
        "classes_track_landings": len(future_to_landings) == len(landing_futures),
        "word_coarser_than_landing": len(future_to_prefixes) < len(landing_futures),
    }


def window_missing_facts(
    windows: list[int],
    *,
    r_max: int = FACT_R_MAX,
    chain_cap: int = CHAIN_CAP,
) -> dict[str, Any]:
    by_window: list[dict[str, Any]] = []
    surviving: set[str] | None = None
    for n_max in windows:
        pe = realized_pe_runs(n_max=n_max, chain_cap=chain_cap)
        cmp = factor_comparison(pe["run_words"], r_max=r_max)
        missing = {r: cmp["missing"]["fact"][r] for r in range(1, r_max + 1)}
        flat = {word for words in missing.values() for word in words}
        surviving = flat if surviving is None else surviving & flat
        by_window.append(
            {
                "n_max": n_max,
                "runs": len(pe["run_words"]),
                "max_run": pe["max_run"],
                "missing_fact": missing,
                "missing_pref": cmp["missing"]["pref"],
                "missing_suff": cmp["missing"]["suff"],
                "fills_factors": cmp["fills_grammar_factors"],
            }
        )
    return {
        "windows": by_window,
        "surviving_missing_facts": sorted(surviving or []),
    }


def itinerary_language_census(
    *,
    n_max: int = N_MAX,
    r_max: int = FACT_R_MAX,
    l_r_max: int = L_R_MAX,
    l_n_max: int | None = None,
    chain_cap: int = CHAIN_CAP,
    windows: tuple[int, ...] | None = None,
) -> dict[str, Any]:
    lang = language_completeness(r_max=l_r_max, n_max=l_n_max or n_max)
    pe = realized_pe_runs(n_max=n_max, chain_cap=chain_cap)
    cmp = factor_comparison(pe["run_words"], r_max=r_max)
    mn = myhill_nerode_proxy(pe)
    growth = None
    if windows:
        growth = window_missing_facts(list(windows), r_max=r_max, chain_cap=chain_cap)
    return {
        "n_max": n_max,
        "language": lang,
        "pe": {
            "runs": len(pe["run_words"]),
            "blocks": len(pe["block_words"]),
            "distinct_run_words": len(set(pe["run_words"])),
            "distinct_block_words": sorted(set(pe["block_words"])),
            "max_run": pe["max_run"],
            "max_run_start": pe["max_run_start"],
            "exits": pe["exits"],
            "terminal_suffixes": pe["terminal_suffixes"],
        },
        "factors": {
            "grammar_counts": cmp["grammar_counts"],
            "realized_counts": cmp["realized_counts"],
            "missing": cmp["missing"],
            "extra": cmp["extra"],
            "fills_grammar_factors": cmp["fills_grammar_factors"],
            "fills_grammar_prefs": cmp["fills_grammar_prefs"],
            "fills_grammar_suffs": cmp["fills_grammar_suffs"],
        },
        "myhill_nerode": mn,
        "window_growth": growth,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }


def ooe_expands_at_five() -> bool:
    return follows_itinerary(5, "OOE") and image_after(5, "OOE") > 5


def oe_never_expands(*, n_max: int = 200) -> bool:
    for n in range(1, n_max + 1):
        if follows_itinerary(n, "OE") and image_after(n, "OE") > n:
            return False
    return True
