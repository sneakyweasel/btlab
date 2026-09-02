# Juggler expanding residual grammar

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Can the actual Juggler residual grammar sustain an infinite sequence of
persistent blocks, each formally expanding
\(3^{\#O(w)}>2^{|w|}\)? Or does the parity/threshold transition
grammar force a contracting block after finitely many steps?

## Exact statement

Keep three notions separate.

1. Syntactic expansion: `expandingItinerary w` means \(2^{|w|}<3^{\#O(w)}\).
   For a residual shape \(O^a E^b\) this is \(2^{a+b}<3^a\), or
   equivalently \(a+b\le\log_2(3^a)\) when \(a\ge 1\), or
   \(b\le\texttt{maxExpandingEvens}(a)\).
2. Realized expansion: a `ResidualStep` whose image strictly exceeds
   the start.
3. Persistent expansion: `PersistentExpandingResidual`.

On the domain \(n\ge 2\),

\[
\texttt{PersistentOddResidual}(x,y)
\iff
\texttt{PersistentExpandingResidual}(x,y).
\]

A contracting itinerary cannot overshoot (`power_bound_contracts`), and
\(2^k=3^o\) is impossible for a nonempty residual. The expanding-word
grammar is therefore the already-known persistence condition
\(T_w(n)>n\) on an odd-to-odd residual, not a new combinatorial
obstruction.

An infinite expanding residual grammar is not an infinite Juggler
orbit. This branch does not claim either.

## Current literature

- Formal exponent gap / `exponentExpanding` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.ItineraryStats`.
- `power_bound_contracts` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Envelope`.
- `PersistentOddResidual` / `PersistentExpandingResidual` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- Two, four, and five consecutive PE blocks —
  **EXACT — LEAN VERIFIED** / **COMPUTATIONALLY VERIFIED** in the
  two-block and expansion-slack dossiers.
- Residual-state finite quotients need the integer itself —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
- Scale-induced near-tightness —
  **PROMOTE** in [juggler_near_tight_scale.md](juggler_near_tight_scale.md).
  Tiny \(q\) does not punish expansion.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Can the realized persistent residual grammar
                        sustain λ>1 indefinitely, or does a finite
                        parity/threshold quotient force a contracting
                        block?
Novelty hypothesis      The expanding-word language, or a small
                        successor-state automaton, is an independent
                        obstruction to an infinite PE chain
Falsifier               Persistence already implies expansion; a
                        type-level cycle disappears under exact
                        landings; the attack reduces to T_w(n)>n
Existing machinery      exponentExpanding, oddEvenBlock,
                        PersistentExpandingResidual, power_bound_contracts,
                        two_block_ooe_365, residual walker
Maximum Phase-0 scope   Combinatorial even-run bound; Persistent⇒Expanding;
                        cheap type-graph / exit census; no halt; no
                        giant state machine
Promotion criterion     Finite M, or a genuinely realizable recurrent
                        expanding grammar that is not T≥n
Stop criterion          Falsifier A–E; machinery gravity; ResidualState
                        replay
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `expandingItinerary` / `expanding_word_ratio` /
  `expanding_implies_odd_density` —
  **EXACT — LEAN VERIFIED**
- `maxExpandingEvens` / `expanding_oddEvenBlock_iff_log` —
  **EXACT — LEAN VERIFIED**
- `persistent_odd_residual_expanding` /
  `persistent_expanding_iff_odd` —
  **EXACT — LEAN VERIFIED**
- Type-level `OOE→OOE` self-loop —
  **EXACT — LEAN VERIFIED** (`expanding_type_ooe_self_loop`); not an
  infinite orbit
- Finite residue-mod-8 expanding automaton —
  **REFUTED** on the scanned window (every odd class both continues
  and exits)
- A finite run bound \(M\) produced by the expanding-word grammar —
  **REFUTED** as a mechanism; a raw finite \(M\) is not proved
- Infinite PE orbit — not claimed

## Experiments

Cheap grammar census, not a new raw search.

- Combinatorial table: \(a=1\Rightarrow b=0\), \(a=2,3\Rightarrow b\le 1\),
  \(a=4,5\Rightarrow b\le 2\), matching \(\log_2(3^a)-a\).
- Odd-odd starts \(n\le 4000\) plus extra landings: the \((a,b)\)
  graph has a recurrent `OOE→OOE` component and many other
  expanding-type edges. Maximum PE run is still \(5\), starting at
  \(2183\). Mean run length does not grow with scale in the window.
- Persistence plus contraction never occurs. Overshoot plus
  contraction never occurs. Both are the envelope theorem, not a
  new census law.
- The realized `OOE→OOE→OOE` chain at \(365\) exits at \(4447\):
  the next `OOE` is expanding and overshoots, but lands odd-to-even.
  The type cycle is Falsifier A.
- PE runs end by leaving the odd-odd frontier after an expanding
  overshoot, or by a contracting descent. Residue modulo \(8\) does
  not predict the exit class.

Tests: `tests/research/juggler_sequence/test_expanding_grammar.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “An expanding persistent residual can be followed by a persistent
  contracting residual.” False for \(n\ge 2\): persistence is
  expansion.
- “The `OOE` type self-loop is an infinite expanding grammar.”
  False: \(365\to 763\to 1749\to 4447\), then
  \(4447\xrightarrow{\mathrm{OOE}}12707\) leaves odd-odd.
- “Residue modulo \(8\) determines whether the next residual stays
  expanding-persistent.” False: every odd class both continues and
  exits.
- “The expanding-word grammar yields a uniform run bound \(M\le 4\).”
  False: the length-\(5\) run at \(2183\), and the Lean-certified
  length-\(4\) run at \(1999\).

## Formalization

`formal/Problems/Juggler/ExpandingGrammar.lean`, after
`NearTightScale` and before `Cycles`. No `sorry`. No halt theorem.
No new residual state object.

## Results

- Syntactic expansion of \(O^a E^b\) is the integer bound
  \(b\le\log_2(3^a)-a\).
- On \(n\ge 2\), `PersistentOddResidual` and
  `PersistentExpandingResidual` coincide.
- The expanding-word language therefore does not constrain a
  persistent chain beyond \(T_w(n)>n\).
- A recurrent type graph exists and is not an orbit grammar.
- Finite residue quotients do not decide continuation.
- An infinite expanding grammar is not proved and not disproved.
  The leftover is whether odd-to-odd landings can continue forever.

## Open questions

Answered in [juggler_landing_parity.md](juggler_landing_parity.md):
\(\theta=\rho/(2T+1)\) is unrestricted on odd-to-odd states and does
not predict the next landing. Do not reopen the weighted-slack
budget or the residual-state tuple.

## Decision

**CLOSE** the expanding-grammar obstruction as
`EXPANDING_GRAMMAR_IS_PERSISTENCE`. Persistence already forces
expansion. The type-level recurrent component is Falsifier A: it
disappears when the landing parity is restored. Finite residues do
not decide continuation. The attack reduces to the endpoint
inequality \(T_w(n)>n\) plus the already-open odd-odd residual
chain. Do not claim a finite run bound. Do not claim an infinite
orbit. Do not claim termination.

Best next question: answered in
[juggler_landing_parity.md](juggler_landing_parity.md).

## Publication assessment

Status: `EXPLORATORY`. An exact identification and a negative
grammar result, not a paper candidate and not a Juggler totality
result.
