# Problem template

Copy this page to `docs/problems/<id>.md` and add `src/research/<id>/` without
editing `bt.*`.

## Problem

Name and one-sentence topic.

## Exact statement

The mathematical question, with quantifiers.

## Current literature

Known results and how this project relates (`known` / `reproduced` /
`extended` / `independent` / `refuted`). Cite `literature/` ids.

## Branch budget

Written before substantial implementation. See
[methodology.md](../methodology.md).

- **Target:** one precise question.
- **Novelty hypothesis:** what could possibly be new.
- **Falsifier:** the observation that kills the idea.
- **Already killed by?:** index cluster, or which of the three tests fails; `none` only with a reason.
- **Existing machinery:** what the platform already provides.
- **Maximum Phase-0 scope:** the smallest experiment that answers the target.
- **Promotion criterion:** what would justify PROMOTE.
- **Stop criterion:** what forces PARK or CLOSE.

## Balanced-ternary formulation

How the objects are written in canonical balanced ternary.

## Why BT may be relevant

Representation, operators, automata, or sparsity — not a claim that BT solves the problem.

## Candidate operations / invariants

Maps and functions to try. Label each claim with a ledger tag from [README.md](../README.md).

## Experiments

Registered runners, ranges, and output schema.

## Conjectures

Ids in `conjectures/`. Computational observations are not conjectures.

## Counterexamples

Smallest witnesses, with tests under `tests/regression/`.

## Formalization

Lean modules, or an explicit statement that none exist yet. No `sorry`.

## Results

Exact theorems and computational verifications.

## Open questions

What remains.

## Decision

`PROMOTE` | `PARK` | `CLOSE`, one short paragraph of justification, and
exactly one best next question. A branch whose statements are all
`KNOWN` or `REPARAMETERIZATION` is a `CLOSE`. Do not continue a branch
automatically.

## Publication assessment

Status: `EXPLORATORY` | `STRUCTURAL` | `THEOREM` | `PAPER_CANDIDATE` | `ARCHIVED`.

`PAPER_CANDIDATE` requires at least one exact theorem or a genuinely
nontrivial computational result with a clear literature distinction.
