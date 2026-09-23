# Juggler–Collatz research map

The lab is dedicated to Juggler and the signed Collatz maps, with the shared exact
mathematics and tools they use.

## Papers and live research

1. [Paper A — Juggler cycle-length bounds](theory/juggler_finite_dynamics_note.md)
2. [Paper B — descent certificates and parity](theory/juggler_parity_discrepancy_note.md)
3. [Paper C — fate contagion](theory/juggler_fate_almost_all_note.md)
4. [Paper D — negative Collatz m-cycles](theory/collatz_3n_minus_1_m_cycles_note.md)
5. [Paper E — Juggler and the signed Collatz maps](theory/juggler_signed_collatz_note.md)

Use the [publication record](theory/paper_deposits.md) for deposited versions,
the paper sources for their current statements, and the
[Juggler](../attacks/juggler/AGENT.md) and [Collatz](../attacks/collatz/AGENT.md)
agent guides for current frontiers. This map
does not duplicate numerical thresholds that can become stale.

The [Collatz mathematics map](collatz_mathematics.md),
[branch ledger](juggler_branch_ledger.md), [theorem ledger](theory/theorem_ledger.md)
and [negative knowledge](negative_knowledge.md) provide the supporting record.
Reviewer exports live in [juggler_review](../juggler_review/); edit their
canonical paper sources and rebuild, rather than editing those copies.

## Evidence labels

- **EXACT — HUMAN PROOF**: a recorded proof with its hypotheses.
- **EXACT — LEAN VERIFIED**: a compiled Lean statement covering the claim.
- **COMPUTATIONALLY VERIFIED**: a finite check on a stated domain.
- **CONJECTURE**: an open statement paired with counterexample search.
- **OBSERVATION**: empirical evidence without a necessity claim.
- **REFUTED**: a recorded counterexample.
- **REPARAMETERIZATION**: a classical construction in local coordinates.

These seven are the ledger's complete vocabulary. Novelty is a separate axis:
KNOWN, PROJECT-SPECIFIC or OPEN. A finite check does not become a theorem, and a
weaker theorem does not establish a global solution. State the exact result and
its quantifiers. See the [research method](methodology.md).

## Build and discovery

- [Architecture and active scope](architecture/overview.md)
- [Lean naming and discovery](architecture/lean_discovery.md)
- [OEIS discovery](architecture/oeis_discovery.md)
- [Research modules](architecture/research_modules.md)
- [Git history and recovery](history.md)
- [Publication privacy and source permissions](publication_safety.md)

Default commands are `python tools/lab.py test` and `python tools/lab.py build`. Earlier projects are available
through Git history. Shared dependencies
stay in the active scope even when they have an older balanced-ternary name.
