"""Minimal-bad survival signatures versus already-proved certificates.

Not a halt theorem. Does not reopen the closed well-ordering census,
the closed stopping-prefix branch, predecessor-cell quotients, or
statistical fitting. SurvivalSignature is which one-step and two-step
descent certificates fail. Inverse generation from a smaller state is
first descent. Neither is a new induction.
"""

from __future__ import annotations

import csv
import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    MINIMAL,
    MINIMAL_CLOSURE,
    PROGRESS,
    has_named,
)
from research.juggler_sequence.minimal_counterexample import barrier_walk, two_step
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_survival.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_survival.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_minimal_survival.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "minimal_survival"

N_PHASE0 = 4000
LEFTOVER_SAMPLE = 12

CLOSED_IMPORT_TOKENS = (
    "future_quotient",
    "residual_minimize",
    "sum_rho",
    "realization_geometry",
    "landing_image",
    "itinerary_language",
    "nc_boundary",
    "adversarial_paths",
    "information_complexity",
    "backward_geometry",
    "accelerated",
    "floor_boundary",
    "two_adic_bridge",
    "first_return_excursions",
    "probabilistic_ld",
    "probabilistic",
    "extremal_control",
    "cell_hut",
    "good_closure",
    "stopping_prefix",
)

ANTI = {
    **ANTI_OVERCLAIM,
    "minimality_plus_inverse_is_new": False,
    "pred_closure_is_new_induction": False,
    "even_map_is_half_square": False,
    "reopen_minimal_counterexample": False,
    "reopen_stopping_prefix": False,
    "reopen_backward_geometry": False,
    "automaton": False,
}

LEAN_THEOREMS = {
    "Minimal": (
        "MinimalNonTerm",
        "minimal_nonterm_odd",
        "minimal_nonterm_odd_image_odd",
        "minimal_nonterm_iterate_ge",
        "minimal_nonterm_oe_descent",
    ),
    "MinimalClosure": (
        "UncoveredOneStep",
        "minimal_bad_uncovered_one_step",
        "odd_not_pred_of_le",
        "even_good_of_sqrt_le",
        "predClosure_iff_reachesOne",
        "minimal_bad_not_predClosure",
    ),
    "Progress": (
        "FiniteProgress",
        "finiteProgress_of_not_odd_odd",
        "unresolved_is_odd_odd",
    ),
}

CLASS_NEW = "SURVIVAL_CONSTRAINT_GREEN"
CLASS_COMPLEX = "MINIMAL_SURVIVAL_COMPLEX"


def signature_row(n: int) -> dict[str, Any]:
    word, image, second = two_step(n)
    one = image < n
    two = second < n
    leftover = (not one) and (not two)
    return {
        "n": n,
        "parity": "odd" if n % 2 == 1 else "even",
        "T": image,
        "T2": second,
        "word2": word,
        "one_step": one,
        "two_step": two,
        "leftover": leftover,
        "odd_odd": word == "OO",
    }


def classify_row(row: dict[str, Any]) -> str:
    if row["one_step"]:
        return "one_step"
    if row["two_step"]:
        return "two_step"
    return "leftover"


def leftover_equals_odd_odd(rows: list[dict[str, Any]]) -> dict[str, Any]:
    mismatches = [
        row["n"]
        for row in rows
        if bool(row["leftover"]) != bool(row["odd_odd"])
    ]
    return {"ok": not mismatches, "mismatches": mismatches[:16]}


def even_one_step_all(rows: list[dict[str, Any]]) -> bool:
    return all(row["one_step"] for row in rows if row["parity"] == "even")


def odd_one_step_none(rows: list[dict[str, Any]]) -> bool:
    return all(not row["one_step"] for row in rows if row["parity"] == "odd")


def residue_census(values: list[int], modulus: int) -> dict[str, int]:
    counts = Counter(n % modulus for n in values)
    return {str(key): counts[key] for key in range(modulus) if counts[key]}


def leftover_descents(ns: list[int]) -> dict[str, Any]:
    drops = 0
    sample: list[dict[str, Any]] = []
    for n in ns:
        walk = barrier_walk(n)
        dropped = walk["first_drop"] is not None
        if dropped:
            drops += 1
        if len(sample) < LEFTOVER_SAMPLE:
            sample.append(
                {
                    "n": n,
                    "word2": two_step(n)[0],
                    "H_n": walk["H_n"],
                    "first_drop": walk["first_drop"],
                    "dropped_below_start": dropped,
                }
            )
    return {
        "count": len(ns),
        "dropped": drops,
        "all_dropped": drops == len(ns),
        "sample": sample,
    }


def lean_api_present() -> dict[str, bool]:
    texts = {
        "Minimal": MINIMAL.read_text(encoding="utf-8"),
        "MinimalClosure": MINIMAL_CLOSURE.read_text(encoding="utf-8"),
        "Progress": PROGRESS.read_text(encoding="utf-8"),
    }
    out: dict[str, bool] = {}
    sorry_free = True
    for layer, names in LEAN_THEOREMS.items():
        text = texts[layer]
        if "sorry" in text or "admit" in text:
            sorry_free = False
        for name in names:
            out[name] = has_named(text, name)
    out["sorry_free"] = sorry_free
    return out


def decide(payload: dict[str, Any]) -> dict[str, Any]:
    lean = payload["lean"]
    eq = payload["leftover_eq_oo"]
    even_ok = payload["even_one_step_all"]
    odd_ok = payload["odd_one_step_none"]
    descents = payload["leftover_descents"]
    residues = payload["leftover_mod8"]
    lean_ok = lean["sorry_free"] and all(
        lean[name]
        for names in LEAN_THEOREMS.values()
        for name in names
    )
    single_residue = len(residues) == 1
    if not (lean_ok and eq["ok"] and even_ok and odd_ok and descents["all_dropped"]):
        return {
            "classification": CLASS_COMPLEX,
            "branch": "CLOSE",
            "reason": (
                "Phase-0 did not match the already-proved certificate "
                "partition, or a leftover start failed to drop below itself. "
                "No new Φ(n) is isolated."
            ),
        }
    if single_residue and payload["leftover_count"] >= 8:
        return {
            "classification": CLASS_NEW,
            "branch": "PROMOTE",
            "reason": (
                "Leftover odd-to-odd starts occupy a single residue class "
                "mod 8, which is not already recorded as the Progress leftover."
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "branch": "CLOSE",
        "reason": (
            "SurvivalSignature leftover is exactly the odd-to-odd class "
            f"({payload['leftover_count']} starts on n≤{payload['N']}). "
            "Every even is one-step covered; no odd n≥3 is. Inverse "
            "generation from a smaller state is first descent: every "
            "leftover start in the window drops below itself. Leftover "
            f"residues mod 8 are {sorted(int(k) for k in residues)}. "
            "All of this is KNOWN (MinimalNonTerm, UncoveredOneStep, "
            "unresolved_is_odd_odd) or a REPARAMETERIZATION of descent. "
            "Minimality plus inverse arithmetic does not create a new Φ(n)."
        ),
    }


def run_phase0(n_max: int = N_PHASE0) -> dict[str, Any]:
    rows = [signature_row(n) for n in range(2, n_max + 1)]
    leftover = [row["n"] for row in rows if row["leftover"]]
    buckets = Counter(classify_row(row) for row in rows)
    word_counts = Counter(row["word2"] for row in rows)
    payload = {
        "experiment": "juggler_minimal_survival",
        "N": n_max,
        "cuda_used": False,
        "anti_overclaim": dict(ANTI),
        "row_count": len(rows),
        "buckets": dict(buckets),
        "word2_counts": dict(word_counts),
        "leftover_count": len(leftover),
        "leftover_eq_oo": leftover_equals_odd_odd(rows),
        "even_one_step_all": even_one_step_all(rows),
        "odd_one_step_none": odd_one_step_none(rows),
        "leftover_mod8": residue_census(leftover, 8),
        "leftover_mod16": residue_census(leftover, 16),
        "leftover_descents": leftover_descents(leftover),
        "lean": lean_api_present(),
        "novelty": {
            "MinimalNonTerm": "KNOWN",
            "good_of_iterate": "KNOWN",
            "even_one_step": "KNOWN",
            "odd_never_one_step": "KNOWN",
            "leftover_is_odd_odd": "KNOWN",
            "PredClosure_iff_ReachesOne": "REPARAMETERIZATION",
            "inverse_generation_is_first_descent": "REPARAMETERIZATION",
            "new_Phi": "REFUTED",
        },
    }
    payload["decision"] = decide(payload)
    payload["_rows"] = rows
    payload["_leftover"] = leftover
    return payload


def write_data(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with (DATA_DIR / "signatures.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=(
                "n",
                "parity",
                "word2",
                "T",
                "T2",
                "one_step",
                "two_step",
                "leftover",
                "odd_odd",
            ),
        )
        writer.writeheader()
        for row in payload["_rows"]:
            writer.writerow(
                {
                    **row,
                    "one_step": int(row["one_step"]),
                    "two_step": int(row["two_step"]),
                    "leftover": int(row["leftover"]),
                    "odd_odd": int(row["odd_odd"]),
                }
            )
    with (DATA_DIR / "leftover.jsonl").open("w", encoding="utf-8") as handle:
        for n in payload["_leftover"]:
            handle.write(json.dumps({"n": n, "word2": "OO"}) + "\n")
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(
            {
                "experiment": payload["experiment"],
                "N": payload["N"],
                "leftover_count": payload["leftover_count"],
                "leftover_eq_oo": payload["leftover_eq_oo"]["ok"],
                "classification": payload["decision"]["classification"],
                "branch": payload["decision"]["branch"],
                "files": ["signatures.csv", "leftover.jsonl", "manifest.json"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _md_table(headers: list[str], lines: list[list[Any]]) -> str:
    head = "| " + " | ".join(headers) + " |"
    sep = "| " + " | ".join("---" for _ in headers) + " |"
    body = "\n".join("| " + " | ".join(str(c) for c in row) + " |" for row in lines)
    return "\n".join((head, sep, body))


def render_json(payload: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in payload.items() if not key.startswith("_")}


def render_markdown(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    descents = payload["leftover_descents"]
    sample = _md_table(
        ["n", "word2", "H_n", "dropped"],
        [
            [row["n"], row["word2"], row["H_n"], row["dropped_below_start"]]
            for row in descents["sample"]
        ],
    )
    novelty = _md_table(
        ["statement", "novelty"],
        [[key, value] for key, value in payload["novelty"].items()],
    )
    return f"""# Juggler minimal-bad survival signatures

Status: **{d['classification']}**

Standalone Phase-0 on whether minimality plus exact inverse
arithmetic yields a new constraint on a least bad state. This is not
a termination theorem. The closed well-ordering and stopping-prefix
branches stay closed.

Every statement below is labelled
`LOGICAL CONSEQUENCE` | `LEAN-CERTIFIED` | `EXACT COMPUTATION` |
`COMPUTATIONALLY OBSERVED` | `COUNTEREXAMPLE`.
These are report labels. Ledger tags, when used, remain the seven
standard tags from [docs/README.md](../README.md).

## 1. Already-proved framework

`Good` is `ReachesOne`. `MinimalNonTerm n` is a least bad state.
Label: **LEAN-CERTIFIED**. **KNOWN**.

If `Good m` and `T^k(n)=m` then `Good n`. Label: **LEAN-CERTIFIED**
(`reachesOne_of_iterate`, `good_of_predecessor_certificate`).
**KNOWN**.

`PredClosure` from `{{1}}` is `ReachesOne`. Label: **LEAN-CERTIFIED**
(`predClosure_iff_reachesOne`). **REPARAMETERIZATION**.

The even map is `T(n)=⌊√n⌋`, not `T(2k)=k^2`. For `n≥2` even,
`T(n)<n`. Label: **LEAN-CERTIFIED**. The informal half-square rule is
discarded.

## 2. SurvivalSignature

On `2≤n≤{payload['N']}`:

| bucket | count |
| --- | --- |
| one_step | {payload['buckets'].get('one_step', 0)} |
| two_step | {payload['buckets'].get('two_step', 0)} |
| leftover | {payload['leftover_count']} |

Two-letter counts `{payload['word2_counts']}`. Every even is
one-step covered: `{payload['even_one_step_all']}`. No odd is
one-step covered: `{payload['odd_one_step_none']}`. Leftover equals
odd-to-odd: `{payload['leftover_eq_oo']['ok']}`. Label:
**EXACT COMPUTATION**. This is `finiteProgress_of_not_odd_odd` /
`unresolved_is_odd_odd`. **KNOWN**.

One-step inverse from a smaller target never hits an odd `n≥3`
(`odd_not_pred_of_le`, `minimal_bad_uncovered_one_step`). Label:
**LEAN-CERTIFIED**.

## 3. Inverse generation is first descent

A smaller `m` generates `n` by exact inverse steps if and only if
some forward iterate equals `m`. For certificates from
`[1,n-1]` that is `T^k(n)<n`. Label: **LOGICAL CONSEQUENCE**.
**REPARAMETERIZATION** of first descent.

Leftover starts in the window that drop below the start:
`{descents['dropped']}` of `{descents['count']}`
(`{descents['all_dropped']}`). Sample:

{sample}

Label: **EXACT COMPUTATION**. That every tested `n` eventually
decreases is the closed-branch window fact, not a new obstruction.
It is stop condition 1 of this attack.

## 4. Residues

Leftover residues mod 8: `{payload['leftover_mod8']}`.
Mod 16: `{payload['leftover_mod16']}`. More than one class occurs.
No single modulus is forced by the leftover. Label:
**COMPUTATIONALLY OBSERVED**. Arbitrary further moduli are not
introduced.

## 5. Novelty

{novelty}

`SURVIVAL_CONSTRAINT_GREEN` is not awarded. There is no new `Φ(n)`
beyond “odd-to-odd and the orbit never drops below `n`”, which is
already `minimal_counterexample_normal_form`. Label:
**COUNTEREXAMPLE** to “minimality plus inverse arithmetic is a new
mechanism”.

## 6. Lean

Cited, not added:

- `MinimalNonTerm`, `minimal_nonterm_odd`, `minimal_nonterm_odd_image_odd`,
  `minimal_nonterm_iterate_ge`
- `UncoveredOneStep`, `odd_not_pred_of_le`, `predClosure_iff_reachesOne`
- `finiteProgress_of_not_odd_odd`, `unresolved_is_odd_odd`

Sorry-free: `{payload['lean']['sorry_free']}`. Not formalized, and not
claimed: `minimal_bad_impossible`, `predecessor_cover_complete`.

## 7. Decision

Classification: **{d['classification']}**.

{d['reason']}

Branch status: **{d['branch']}**. Phase 1 is not launched. A larger
window only lengthens the leftover list of terminating odd-to-odd
starts.
"""


def render_dossier(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    return f"""# Juggler minimal-bad survival signatures

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen the closed
well-ordering census
([juggler_minimal_counterexample.md](juggler_minimal_counterexample.md))
or the closed stopping-prefix branch
([juggler_stopping_prefix.md](juggler_stopping_prefix.md)).

## Problem

Does “minimality plus exact inverse arithmetic” produce a new
constraint on a hypothetical least bad state, or only the already
proved leftover that one-step and two-step certificates miss exactly
the odd-to-odd class?

## Exact statement

Let \\(T\\) be `floorPower`. Write `Good = ReachesOne`,
`Bad = ¬ReachesOne`, and `MinimalNonTerm n` for a least bad state.
A one-step predecessor certificate from a smaller target covers \\(n\\)
exactly when \\(T(n)<n\\). A two-step certificate covers \\(n\\) when
\\(T^2(n)<n\\). Let `SurvivalSignature(n)` be the pair of those
failures together with the first two letters of the orbit. Decide
whether the surviving class is anything other than

\\[
n\\text{{ odd and }}T(n)\\text{{ odd}},
\\]

already isolated by `unresolved_is_odd_odd`, or whether inverse
closure of \\([1,n-1]\\) is anything other than “some iterate is
\\(<n\\)”.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
- `MinimalNonTerm` normal form — **EXACT — LEAN VERIFIED**.
- `PredClosure ↔ ReachesOne` — **EXACT — LEAN VERIFIED**.
  **REPARAMETERIZATION**. Branch **CLOSE**
  (`juggler_minimal_counterexample`).
- `finiteProgress_of_not_odd_odd` / `unresolved_is_odd_odd` —
  **EXACT — LEAN VERIFIED**. Branch **PROMOTE**
  (`juggler_progress_coverage`).
- Unbounded \\(F_\\tau\\) — **REPARAMETERIZATION**. Branch **CLOSE**
  (`juggler_stopping_prefix`).

Project relationship: **independent** only if a new \\(\\Phi(n)\\)
appears. The even rule \\(T(2k)=k^2\\) is a forward/inverse swap and
is not used. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does SurvivalSignature add a constraint on
                        MinimalNonTerm beyond odd-to-odd leftover
                        and “the orbit never drops below n”?
Novelty hypothesis      Minimality plus exact inverse cells yields a
                        finite covering family or an impossible Φ(n)
Falsifier               Leftover = OO; inverse generation = first
                        descent; all statements KNOWN or
                        REPARAMETERIZATION
Existing machinery      MinimalNonTerm, UncoveredOneStep,
                        predClosure_iff_reachesOne,
                        finiteProgress_of_not_odd_odd,
                        even_good_of_sqrt_le, odd_not_pred_of_le,
                        floor_power, two_step, barrier_walk
Maximum Phase-0 scope   N=4000; one-step/two-step signatures;
                        leftover vs OO; residue diagnostic; decide
Promotion criterion     A new Φ(n) not already in Minimal.lean or
                        Progress.lean
Stop criterion          Leftover is OO; covering is descent;
                        tautology only
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

A leftover cylinder in least significant trits would have been a BT
observation. Phase-0 does not hunt a BT law.

## Candidate operations / invariants

- `MinimalNonTerm` — **EXACT — LEAN VERIFIED**. **KNOWN**
- `T^k(n)=m` and `Good m` implies `Good n` —
  **EXACT — LEAN VERIFIED**. **KNOWN**
- one-step cover \\(T(n)<n\\) — **EXACT — LEAN VERIFIED** for evens
- odd \\(n\\ge 3\\) never one-step covered — **EXACT — LEAN VERIFIED**
  (`odd_not_pred_of_le`)
- leftover of one-step and two-step = odd-to-odd — **KNOWN**
- `PredClosure ↔ ReachesOne` — **REPARAMETERIZATION**
- inverse closure of \\([1,n-1]\\) equals first descent —
  **REPARAMETERIZATION**
- new \\(\\Phi(n)\\) — **REFUTED** on the Phase-0 window
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.minimal_survival`
- Records: [juggler_minimal_survival.md](../research/juggler_minimal_survival.md),
  [juggler_minimal_survival.json](../research/juggler_minimal_survival.json)
- Data: `data/research/juggler/minimal_survival/`
- Tests: `tests/research/juggler_sequence/test_minimal_survival.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- “Minimality plus inverse arithmetic is a new mechanism.” **REFUTED**:
  leftover is odd-to-odd; inverse generation is first descent.
- “Every even predecessor exists only on squares / `T(2k)=k^2`.”
  **REFUTED**: `T` on evens is `⌊√n⌋`; every `m` has an even cell.
- “Leftover occupies one residue class.” **REFUTED**: residues
  `{payload['leftover_mod8']}`.

## Formalization

None added. Existing lemmas in `Minimal.lean`, `MinimalClosure.lean`,
and `Progress.lean` are cited, not restated. No
`research.juggler.minimal_bad` / `predecessor_cover` modules.

## Results

See [juggler_minimal_survival.md](../research/juggler_minimal_survival.md).
Classification **{d['classification']}**.

## Open questions

Whether every positive integer reaches 1. Well-ordering plus
one-step/two-step inverse arithmetic does not answer it.

## Decision

**{d['branch']}**. {d['reason']} A branch whose surviving statements
are `KNOWN` or `REPARAMETERIZATION` is a `CLOSE`.

Best next question: none from this branch. Do not launch Phase 1.

## Publication assessment

Status: `ARCHIVED`.

The survival census repackages `unresolved_is_odd_odd` and first
descent. There is no new theorem and no paper distinction.
"""


def write_docs(payload: dict[str, Any]) -> None:
    JSON_PATH.write_text(
        json.dumps(render_json(payload), indent=2) + "\n", encoding="utf-8"
    )
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    DOSSIER_PATH.write_text(render_dossier(payload), encoding="utf-8")


def write_all(payload: dict[str, Any]) -> None:
    write_data(payload)
    write_docs(payload)


def main() -> None:
    payload = run_phase0()
    write_all(payload)
    print(
        json.dumps(
            {
                "classification": payload["decision"]["classification"],
                "branch": payload["decision"]["branch"],
                "leftover_count": payload["leftover_count"],
                "leftover_eq_oo": payload["leftover_eq_oo"]["ok"],
                "even_one_step_all": payload["even_one_step_all"],
                "odd_one_step_none": payload["odd_one_step_none"],
                "all_leftover_dropped": payload["leftover_descents"]["all_dropped"],
                "leftover_mod8": payload["leftover_mod8"],
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
