"""Bounded exact controls for Euclidean induction; never searches for cycles."""
from __future__ import annotations

from math import gcd, isqrt
import json

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import (
    ABSOLUTE_CELL_THRESHOLD_CYCLES,
    certify_cycle,
)

WORDS = ("O", "OE", "OOE", "OOEOE", "OOEOOEOE",
         "OOE" + "OOEOOEOE", "OOE" + "OOEOOEOE" * 2)


def trace_word(x: int, word: str) -> list[int]:
    """Execute prescribed branches, independently of their parity guards."""
    states = [x]
    for letter in word:
        if letter not in "OE":
            raise ValueError("unknown branch")
        x = isqrt(x**3 if letter == "O" else x)
        states.append(x)
    return states


def parity_guard(states: list[int], word: str) -> bool:
    return all(bool(x % 2) == (w == "O") for x, w in zip(states[:-1], word))


def rank_induction(a: int, b: int) -> list[dict]:
    """Check each symbolic stage against literal original first returns."""
    if a <= 0 or b <= 0:
        raise ValueError("positive branch lengths required")
    original_a, original_b, length = a, b, a+b
    A, B = "O", "E"
    stages = []
    while True:
        n = a+b
        covered = []
        towers = []
        for base in range(n):
            word = A if base < a else B
            i, actual_word, tower = base, "", []
            while True:
                tower.append(i)
                actual_word += "O" if i < original_a else "E"
                i = (i+original_b) % length
                if i < n:
                    break
            assert actual_word == word
            assert i == (base+b) % n
            covered.extend(tower)
            towers.append({"base": base, "word": word, "ranks": tower, "image": i})
        assert sorted(covered) == list(range(length))
        assert a*len(A)+b*len(B) == length
        assert a*A.count("O")+b*B.count("O") == original_a
        assert a*A.count("E")+b*B.count("E") == original_b
        stages.append({"a": a, "b": b, "A": A, "B": B, "towers": towers})
        if a == 0 or b == 0:
            assert n == gcd(original_a, original_b)
            break
        if a >= b:
            a, B = a-b, A+B
        else:
            b, A = b-a, A+B
    return stages


def source_controls() -> list[dict]:
    """Recheck exactly the original 3..65535 sample, with integer powers."""
    records = []
    for word in WORDS:
        numerator, denominator = 3**word.count("O"), 2**len(word)
        valid, cubic, failures = 0, 0, []
        for x in range(3, 65536, 2):
            states = [x]
            y = x
            for letter in word:
                if bool(y % 2) != (letter == "O"):
                    break
                y = isqrt(y**3 if letter == "O" else y)
                states.append(y)
            if len(states) != len(word)+1 or not y % 2:
                continue
            valid += 1
            if max(states) >= min(states)**3:
                continue
            cubic += 1
            # For an odd y, this pair is precisely odd_floor(x^(num/den))=y.
            power = x**numerator
            assert y**denominator <= power
            if power >= (y+2)**denominator:
                failures.append({"x": x, "y": y, "states": states})
        records.append({"word": word, "numerator": numerator, "denominator": denominator,
                        "odd_sources_checked": 32767, "parity_valid_odd_endpoints": valid,
                        "also_cubic_height": cubic, "projection_failures": failures})
    return records


def report() -> dict:
    for a in range(1, 33):
        for b in range(1, 33):
            rank_induction(a, b)
    cycles = []
    for threshold, cyclic in ABSOLUTE_CELL_THRESHOLD_CYCLES:
        certificate = certify_cycle(threshold, list(cyclic))
        values = sorted(cyclic)
        odd = certificate["odd_branch_count"]
        stages = rank_induction(odd, len(values)-odd)
        mismatches = sum(bool(x % 2) != (i < odd) for i, x in enumerate(values))
        for stage in stages:
            failed_guards, tested_sources = 0, 0
            for tower in stage["towers"]:
                trace = trace_word(values[tower["base"]], tower["word"])
                assert trace == [values[i] for i in tower["ranks"]] + [values[tower["image"]]]
                failed_guards += sum(bool(x % 2) != (w == "O")
                                     for x, w in zip(trace[:-1], tower["word"]))
                tested_sources += len(tower["word"])
            assert failed_guards == mismatches and tested_sources == len(values)
        cycles.append({"threshold": threshold, "minimum": values[0], "period": len(values),
                       "stages": len(stages), "parity_mismatches_at_every_stage": mismatches,
                       "terminal_word": stages[-1]["towers"][0]["word"],
                       "actual_juggler_cycle": False})
    guards = []
    for s in (3, 5, 101):
        states, b = trace_word(s**4, "OE"), s**3
        assert states == [s**4, s**6, s**3]
        assert b <= states[0] < b*b == states[1] < b**3
        assert states[-1] == b and all(x % 2 for x in states)
        assert not parity_guard(states, "OE")
        guards.append({"s": s, "threshold": b, "states": states,
                       "odd_endpoints": True, "hidden_even_guard": False})
    return {"scope": {"odd_source_range": [3, 65535], "words": list(WORDS),
                       "rank_branch_length_range": [1, 32], "rank_pairs": 1024,
                       "archived_threshold_cycles": 7, "cycle_search": False},
            "arithmetic": "Exact integers throughout; no numerical roots or logarithms",
            "sources": source_controls(), "archived_cycles": cycles,
            "hidden_guard_examples": guards,
            "uniform_endpoint_closure_proved": False,
            "uniform_parity_closure_proved": False, "no_cycle_proved": False}


if __name__ == "__main__":
    data = report()
    out = DATA_ROOT / "cycle_cubic_induction" / "controls.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "sources": data["sources"],
                      "no_cycle_proved": data["no_cycle_proved"]}, indent=2))
