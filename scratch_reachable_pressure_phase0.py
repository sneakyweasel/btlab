import math
import statistics
import time
from collections import defaultdict


P19 = (1.0 - 1.0 / 19.0) / math.log2(3.0)
THETA = math.log(P19 / (1.0 - P19))
X = math.exp(THETA)
A = (1.0 + X) / 2.0
A4 = A**4
POSITIVE_WORDS = {"EOOO", "OEOO", "OOEO", "OOOE", "OOOO"}


def juggler(n: int) -> int:
    if n % 2 == 0:
        return math.isqrt(n)
    return math.isqrt(n * n * n)


def log10_int(n: int) -> float:
    if n <= 0:
        return float("-inf")
    bits = n.bit_length()
    shift = max(0, bits - 53)
    return math.log10(n >> shift) + shift * math.log10(2.0)


def analyze(name: str, starts: range, n0: int, dmax: int, bit_cap: int = 10_000_000):
    # The two fields are tilted mass and number of original ancestors.
    states = {n: (1.0, 1) for n in starts if n > n0}
    rows = []
    capped_events = 0
    started = time.time()

    for depth in range(dmax + 1):
        if not states:
            break
        mass = sum(value[0] for value in states.values())
        ancestor_count = sum(value[1] for value in states.values())
        word_mass = defaultdict(float)
        mass_after_four = 0.0
        positive_excess = 0.0
        total_excess = 0.0
        dies_within_four = 0.0

        for state, (weight, multiplicity) in states.items():
            image = state
            letters = []
            live = True
            for _ in range(4):
                letters.append("O" if image % 2 else "E")
                if image % 2 and image.bit_length() * 3 > bit_cap:
                    live = False
                    capped_events += multiplicity
                    break
                image = juggler(image)
                if image <= n0:
                    live = False
                    break
            if live:
                word = "".join(letters)
                odd_count = word.count("O")
                multiplier = X**odd_count
                word_mass[word] += weight
                mass_after_four += weight * multiplier
                total_excess += weight * (multiplier - A4)
                if word in POSITIVE_WORDS:
                    positive_excess += weight * (multiplier - A4)
            else:
                dies_within_four += weight
                total_excess -= weight * A4

        keys = sorted(states)
        adjacent = sum(1 for state in keys if state + 1 in states)
        adjacent_overlap = sum(
            min(states[state][0], states[state + 1][0])
            for state in keys
            if state + 1 in states
        )
        gaps = [keys[index + 1] - keys[index] for index in range(len(keys) - 1)]
        positive_mass = sum(word_mass[word] for word in POSITIVE_WORDS)
        positive_future_mass = sum(
            word_mass[word] * X ** word.count("O") for word in POSITIVE_WORDS
        )
        rows.append(
            {
                "depth": depth,
                "live_ancestors": ancestor_count,
                "support": len(states),
                "ratio4": mass_after_four / (A4 * mass),
                "positive_share": positive_mass / mass,
                "positive_future_share": (
                    positive_future_mass / mass_after_four if mass_after_four else 0.0
                ),
                "positive_excess": positive_excess / (A4 * mass),
                "net_excess": total_excess / (A4 * mass),
                "death4": dies_within_four / mass,
                "max_atom": max(weight for weight, _ in states.values()) / mass,
                "energy": sum(weight**2 for weight, _ in states.values()) / mass**2,
                "count_energy": (
                    sum(multiplicity**2 for _, multiplicity in states.values())
                    / ancestor_count**2
                ),
                "max_ancestry": max(multiplicity for _, multiplicity in states.values()),
                "mean_ancestry": ancestor_count / len(states),
                "weighted_ancestry": (
                    sum(weight * multiplicity for weight, multiplicity in states.values())
                    / mass
                ),
                "tv_ratio": (2.0 * mass - 2.0 * adjacent_overlap) / mass,
                "adjacent_pairs": adjacent,
                "log10_density": (
                    math.log10(len(keys)) - log10_int(keys[-1] - keys[0] + 1)
                    if len(keys) > 1
                    else 0.0
                ),
                "gap_min": min(gaps) if gaps else 0,
                "gap_median_log10": (
                    log10_int(statistics.median_low(gaps)) if gaps else 0.0
                ),
                "word_shares": {
                    word: word_mass[word] / mass for word in sorted(POSITIVE_WORDS)
                },
            }
        )

        next_states = {}
        for state, (weight, multiplicity) in states.items():
            if state % 2 and state.bit_length() * 3 > bit_cap:
                capped_events += multiplicity
                continue
            image = juggler(state)
            if image <= n0:
                continue
            next_weight = weight * (X if state % 2 else 1.0)
            if image in next_states:
                old_weight, old_multiplicity = next_states[image]
                next_states[image] = (
                    old_weight + next_weight,
                    old_multiplicity + multiplicity,
                )
            else:
                next_states[image] = (next_weight, multiplicity)
        states = next_states

    maxima = {
        key: (max(rows, key=lambda row: row[key])["depth"], max(row[key] for row in rows))
        for key in (
            "ratio4",
            "positive_share",
            "positive_excess",
            "max_atom",
            "energy",
            "max_ancestry",
            "weighted_ancestry",
        )
    }
    selected_depths = {
        0,
        1,
        5,
        10,
        16,
        20,
        30,
        35,
        dmax,
        *(depth for depth, _ in maxima.values()),
    }
    print()
    print(
        "COHORT",
        name,
        "N0",
        n0,
        "starts",
        len(starts),
        "seconds",
        round(time.time() - started, 3),
        "capped_events",
        capped_events,
    )
    print("PARAMETERS", {"theta": THETA, "x": X, "a4": A4})
    print("MAXIMA", maxima)
    for row in rows:
        if row["depth"] not in selected_depths:
            continue
        print(
            "ROW",
            {
                key: row[key]
                for key in (
                    "depth",
                    "live_ancestors",
                    "support",
                    "ratio4",
                    "positive_share",
                    "positive_future_share",
                    "positive_excess",
                    "death4",
                    "max_atom",
                    "energy",
                    "max_ancestry",
                    "mean_ancestry",
                    "weighted_ancestry",
                    "tv_ratio",
                    "adjacent_pairs",
                    "log10_density",
                    "gap_min",
                    "gap_median_log10",
                )
            },
            "WORDS",
            row["word_shares"],
        )
    return rows


if __name__ == "__main__":
    analyze(
        "full odd dyadic (1e6,2e6]",
        range(1_000_001, 2_000_001, 2),
        260,
        35,
    )
