# Laboratory architecture

The laboratory contains Juggler and signed Collatz research, their mathematical
dependencies, and publication/discovery tooling.

```text
cli                         Collatz commands and laboratory status
research.juggler_sequence    Juggler research
research.collatz            signed Collatz research
research.syracuse            Syracuse experiments
research.collatz_finite_descent  finite descent experiments
research_engine             shared exact experimental dynamics
bt                          shared balanced-ternary arithmetic
```

`bt` must not import `research` or `research_engine`. Mathematical research must
not import a UI. The Streamlit UI, unrelated applications and their entry points
are removed. The Juggler companion website remains in `web/juggler-companion/`.

`research.experiments` provides shared table schemas and writers;
`research.open_problems` lists the four applications. `research.conjectures`
and `research.literature` read their supporting registries. These are infrastructure,
not additional research programmes.

Collatz outputs live in `data/research/collatz/`, including finite-descent and
Syracuse records. CLI writers resolve this location from their source checkout,
so running a command elsewhere does not create another output tree. Generated
`raw/`, `derived/`, and `reports/` subdirectories are ignored; curated evidence
and archived YAML records remain tracked.

Lean modules are retained through Juggler/Collatz imports and current ledger
citations, including their transitive dependencies. The library barrels contain
only retained imports. Build with
`python tools/lab.py build` or `lake build` in `formal/`; test with `pytest`.
Paper-pinned mathematical sources and the Lake package configuration remain stable.

Earlier sources are recoverable from [Git history](../history.md).

Local generated state belongs in the ignored `.cache/` (Formalpedia and Python
tool caches) and `.build/` (paper builds and other disposable build output).
Pytest, Hypothesis, Ruff, and mypy use subdirectories of `.cache/`; ordinary
pytest temporary files use the system temporary directory.

The hidden configuration directories remain part of the working laboratory:
`.github/` holds CI, `.cursor/` holds research rules and skills, and `.claude/`
holds research skills and the companion website launcher. Local Git worktrees
can also live under `.claude/worktrees/`; manage them with Git rather than
deleting that directory. `.vscode/` contains optional local Lean editor settings.
