# Local Arb MCP

The Arb MCP gives agents bounded, reproducible real interval calculations using
the lab's [FLINT/Arb primitives](certified_numerics.md). It is a separate local
stdio service; Formalpedia remains a discovery service. No API key is needed.

## Tools and workflow

| Tool | Purpose |
|---|---|
| `arb_capabilities` | Backend versions, checkout, language, budgets and examples |
| `arb_evaluate` | Outward enclosure of an expression over exact point or interval inputs |
| `arb_compare` | Adaptive true / false / unresolved comparison with a residual enclosure |
| `arb_production_root` | Unique root bracket for a positive, decreasing production sum |
| `arb_continued_fraction` | Certified leading partial quotients and last convergent; exact for a bare rational |
| `arb_paper_c_models` | The twelve canonical models from the existing Paper C audit |
| `arb_paper_c_rate` | Test one integer depth against a specified contagion exponent |

Start with `arb_capabilities`. Write the intended exact expression and its domain,
then evaluate or compare it. Keep the complete structured response: it includes
the request, backend versions, source hashes, outward rational bounds and precision.
The decimal display includes its radius; never use its midpoint as a certificate.
The hashes describe local implementation sources, not a signed or Lean certificate.
Publish durable evidence through a deliberate audit with a research manifest;
MCP calls do not write reports, update the ledger or change evidence labels.

Resources `arb://guide` and `arb://capabilities` expose this guide and current
capabilities. All seven tools have structured outputs and read-only annotations.

## Exact expression language

Expressions accept decimal/integer literals, scientific notation, parentheses,
`+`, `-`, `*`, `/`, `**`, the constant `pi`, and unary functions `sqrt`, `log`
(natural logarithm), `exp`, `sin`, `cos`, `atan`, `abs`. Decimal tokens are parsed
as exact rationals from the original text: `0.1` means exactly one tenth.
Use `**` for powers; `^`, Python objects, attributes, indexing and arbitrary
function calls are rejected. This is an AST interpreter, never Python `eval`.

Variables map names to exact strings or two-element arrays of endpoint strings:

```json
{"expression":"log(x)/log(3)","variables":{"x":["2","3"]},"bits":256}
```

This encloses the expression uniformly over the entire closed input interval.
Distinct variables range independently. Interval dependency can widen a bound:
even `x-x` may produce a nonzero-width enclosure. Splitting a domain may help,
but callers must justify coverage when assembling a uniform bound. Raising
precision cannot remove genuine input uncertainty. Equality of two rounded
expressions can remain unresolved even when a symbolic proof is easy.

Comparison example, passed to `arb_compare`:

```json
{"left":"sqrt(2)","right":"7/5","relation":">","bits":128,"max_bits":4096}
```

`status="certified", holds=true` establishes the requested relation uniformly
over the input box; `holds=false` establishes its negation uniformly.
`status="unresolved", holds=null` establishes neither. Overlap and nonfinite
results never become false certificates. Comparison retries reconstruct every
intermediate at increasing precision. Unsupported syntax and exceeded budgets
return MCP errors; domain failures return unresolved, with a reason. Evaluations
return `status="enclosed"` when finite and `unresolved` otherwise.

## Paper examples

The [all-paper audit](../research/arb_paper_audit.md) exercises the actual
stdio service against Papers A–E and the Beatty companion, preserves full
responses and records the mathematical consequences and their boundaries.
Run `python tools/check_papers_arb.py --paper A E Beatty` to regenerate
selected reports, or supply `--output-root .build/arb-review` for a separate
run. The audit performs exact enumeration outside the MCP and all
certified transcendental evaluations through it.

Call `arb_paper_c_models`, select `models.OOEE_fixed`, and pass those terms to
`arb_production_root`. The equivalent explicit request is:

```json
{"terms":[["1","1/2"],["33/100","3/4"],["11/100","9/16"]],"digits":24}
```

The resulting root bracket lies near `0.626551756400580`. Positivity of every
coefficient and bases strictly between zero and one imply continuity and strict
decrease. Certified endpoint signs then establish a unique root. The root tool
is deliberately restricted to this family; it does not infer these properties
for an arbitrary expression or general root finder.

For the written `5/8` contagion exponent, `arb_paper_c_rate` with
`{"C":16,"q":"1/2","kind":"Chernoff","exponent":"5/8"}` certifies the
rate exceeds `3/8`. At `C=15` it certifies the inequality is false. One call does
not establish minimality: the canonical full audit checks all preceding integer
depths. Use `exponent="100/203"` for the formal baseline. Model and rate checks
do not establish production, cylinder, pressure or admissible-error hypotheses.

## Execution limits and isolation

Each computation runs in a fresh Python process, with this checkout's sources
explicitly bound and Python bytecode writing disabled. At most two workers run
at once; each has a 20-second deadline and queue waiting has a separate 20-second
limit. Timeout or cancellation kills and reaps the child. This isolates FLINT's
global precision context and C-level failures between requests.

Inputs are capped at 32 KiB, expressions at 2048 characters / 160 AST nodes /
24 levels, and variables at 24. Precision is 32–4096 bits. Exact number strings
are at most 128 characters, with decimal exponents of absolute value at most
256. Intermediate magnitudes are bounded by `2**1024`; dyadic exponents below
`-8192` are rejected before rational endpoint export. Power exponents must lie
within `[-256,256]` and `exp` arguments within `[-700,700]`. Noninteger powers
require a certified positive base. These conservative limits may reject valid
mathematics; use a reviewed Python audit for larger work.

Production roots accept up to 32 terms, 1–100 decimal width digits, and
`0 <= lower < upper <= 16`. Rate checks accept integer depths 5–10000.
Continued fractions accept 1–1000 terms and return only terms whose floor is
certain over the whole enclosure; an unresolved result keeps its certified prefix.
Responses are capped at 128 KiB. The service offers no arbitrary code, file
paths, networking or artifact writes. Process isolation is a resource and
precision boundary, not an operating-system security sandbox.

## Setup and verification

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
python tools/arb_mcp.py
python tools/lab.py test -- tests/research_engine/test_arb_expressions.py tests/tools/test_arb_mcp.py
```

Register the absolute interpreter and server script paths. The portable
[configuration template](../../tools/arb_mcp.example.json) also works with
clients using an `mcpServers` object. Codex registration follows the
[official MCP setup](https://learn.chatgpt.com/docs/extend/mcp?surface=cli):

```text
codex mcp add btlab-arb --env PYTHONUTF8=1 -- <absolute-python> -B <absolute-checkout>/tools/arb_mcp.py
```

Reconnect the client to load a newly configured server. For a worktree, register
the script inside that worktree: `arb_capabilities.root` identifies the selected
checkout. Existing processes need reconnection after implementation changes.
The transport tests start a fresh stdio server, check Paper C examples and
concurrent precision isolation, and confirm errors leave it usable.

Numerical enclosures are finite computational evidence. They do not discharge
an infinite tail, uniform asymptotic error, analytic model assumption or Lean
proof obligation. Retain stronger exact integer/rational checks where available.
