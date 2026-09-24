"""Does each ``EXACT — LEAN VERIFIED`` ledger row carry the Lean evidence its label claims?

Two checks. The static one needs only the ledger: a row with that label must name the
declarations it rests on (``decl``), or no tool can connect the label to Lean. Rows that
named none when this gate was introduced are held in a baseline that may only shrink.

The compiled one reads the formalpedia semantic export, which records Lean's own
``collectAxioms`` for every declaration of the local library. Each named declaration must
be in the current export, and its axioms must be the ones its row's ``lean_trust`` allows:
Mathlib's three for ``kernel``, those plus the compiler-trust axioms for declarations a
``mixed`` or ``compiler`` row lists, and never ``sorryAx``. The export is produced by CI's
Lean job (``python tools/lab.py build``). Neither check decides whether a declaration
covers the English claim; that remains a reading of the statements.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from . import identities as _fp_identities
from . import workspace as _fp_workspace
from .audits import STANDARD


LABEL = 'EXACT — LEAN VERIFIED'
COMPILER_AXIOMS = frozenset({'Lean.ofReduceBool', 'Lean.trustCompiler'})
BASELINE_NAME = 'data/research/formalpedia/lean_verified_without_declarations.json'


def lean_rows(ledger: list[dict]) -> list[dict]:
    return [row for row in ledger if row.get('tag') == LABEL]


def unnamed(ledger: list[dict]) -> list[str]:
    return sorted(row['id'] for row in lean_rows(ledger) if not _fp_identities.row_decls(row))


def baseline(root: Path | None = None) -> list[str]:
    path = (root or _fp_workspace.ROOT) / BASELINE_NAME
    return sorted(json.loads(path.read_text(encoding='utf-8'))['rows'])


def static_problems(ledger: list[dict], allowed: list[str]) -> list[dict[str, Any]]:
    now, held = set(unnamed(ledger)), set(allowed)
    problems = [{'kind': 'lean_verified_without_declaration', 'row': row,
                 'detail': 'name the declarations in `decl`; the baseline only holds older rows'}
                for row in sorted(now - held)]
    problems += [{'kind': 'baseline_entry_resolved', 'row': row,
                  'detail': f'the row now names its declarations or lost the label; remove it '
                            f'from {BASELINE_NAME}'}
                 for row in sorted(held - now)]
    return problems


def _allowed(row: dict, name: str) -> frozenset[str]:
    trust = row.get('lean_trust')
    if trust == 'compiler' or (trust == 'mixed' and name in (row.get('compiler_decls') or [])):
        return frozenset(STANDARD) | COMPILER_AXIOMS
    return frozenset(STANDARD)


def compiled_problems(index: dict, ledger: list[dict], axioms_of) -> dict[str, Any]:
    """``axioms_of(identities) -> {identity: list | None}``, normally the semantic export."""
    targets, problems = [], []
    for row in lean_rows(ledger):
        for name in _fp_identities.row_decls(row):
            found = _fp_identities.resolve_declarations(
                index, name, file=_fp_identities.lean_key(row.get('lean')))
            if len(found) != 1 or not found[0].get('qualified_name'):
                problems.append({'kind': 'declaration_unresolved', 'row': row['id'], 'name': name,
                                 'candidates': len(found)})
                continue
            targets.append((row, name, found[0]['module'] + '::' + found[0]['qualified_name']))
    recorded = axioms_of(sorted({identity for _, _, identity in targets})) if targets else {}
    checked = 0
    for row, name, identity in targets:
        axioms = recorded.get(identity)
        if axioms is None:
            problems.append({'kind': 'not_in_current_export', 'row': row['id'], 'identity': identity})
            continue
        checked += 1
        extra = sorted(set(axioms) - _allowed(row, name))
        if extra:
            problems.append({'kind': 'axioms_exceed_label', 'row': row['id'], 'identity': identity,
                             'lean_trust': row.get('lean_trust'), 'unexpected_axioms': extra})
    return {'declarations_checked': checked, 'declarations_named': len(targets), 'problems': problems}


def check(index: dict, ledger: list[dict], *, root: Path | None = None, semantic=None,
          require_compiled: bool = False) -> dict[str, Any]:
    rows = lean_rows(ledger)
    result = {'label': LABEL, 'rows': len(rows),
              'rows_naming_declarations': len(rows) - len(unnamed(ledger)),
              'problems': static_problems(ledger, baseline(root)),
              'baseline_rows': len(baseline(root))}
    if semantic is None:
        from .semantic_query import SemanticCatalogue
        semantic = SemanticCatalogue(root) if root else SemanticCatalogue()
    try:
        compiled = compiled_problems(index, ledger, lambda ids: semantic.axioms(ids)['axioms'])
    except (ValueError, OSError) as exc:
        result['compiled'] = {'status': 'unavailable', 'reason': str(exc)}
        if require_compiled:
            result['problems'].append({'kind': 'compiled_export_unavailable', 'detail': str(exc)})
        return result
    result['compiled'] = dict(status='checked', declarations_checked=compiled['declarations_checked'],
                              declarations_named=compiled['declarations_named'])
    result['problems'] += compiled['problems']
    return result
