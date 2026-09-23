# Collatz research data

This directory holds the outputs of the signed Collatz, finite-descent, and
Syracuse research code.

| Location | Contents |
|---|---|
| Top-level JSON files | Curated fibre-mass computations kept in Git |
| `finite_descent/` | Retained YAML records from the archived shortcut investigation |
| `syracuse/` | Syracuse attack records, created when written |
| `raw/` | Generated tables and reproducibility manifests, ignored by Git |
| `reports/` | Generated summaries, ignored by Git |
| `derived/` | Derived experiment outputs, ignored by Git |

Collatz CLI commands write here when passed `--write`. The default location is
anchored to the checkout supplying the Python code. Python experiment functions
also accept an explicit output directory.

Run commands through `python tools/lab.py run cli.main collatz ...` to select
this checkout's imports. Existing local datasets were moved here from the former
root `experiments/` directory; their manifest artifact paths were updated.
