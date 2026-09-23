---
name: add-ledger-row
description: Add or retag a theorem-ledger row from JSON and regenerate the markdown. Use when adding a named theorem, changing a claim tag, or editing docs/theory/theorem_ledger.json.
---

# Add a theorem-ledger row

`docs/theory/theorem_ledger.json` is the source of truth.
`docs/theory/theorem_ledger.md` is generated. Never edit the markdown by hand.

## Tags

Use exactly one:

- `EXACT — HUMAN PROOF`
- `EXACT — LEAN VERIFIED`
- `COMPUTATIONALLY VERIFIED`
- `CONJECTURE`
- `OBSERVATION`
- `REFUTED`
- `REPARAMETERIZATION`

Do not write `PROVED` or `VERIFIED COMPUTATIONALLY` in the JSON or in docs. `tools/render_theorem_ledger.py` rejects anything outside this list.

`KNOWN`, `PROJECT-SPECIFIC`, and `OPEN` are novelty annotations for prose, never ledger tags.

Empty `lean` is allowed only when the tag is **not** `EXACT — LEAN VERIFIED`.
Every `source`, `tests[]`, and nonempty `lean` path must exist. Use the current
schema's repository-relative paths, including `formal/` for Lean files.

## Steps

1. Choose a stable unique id: `J-…` for Juggler, `C-…` for Collatz, or an
   existing shared-mathematics prefix when that is the actual scope.
2. Append an object with `id`, `tag`, `statement`, `source`, `lean`, `tests`, `related_conjectures`.
3. Point `tests` at files that actually exist (`tests/unit/…` or `tests/research/…`).
4. From the repo root:

```powershell
python tools/render_theorem_ledger.py
python tools/render_theorem_ledger.py --check
python tools/lab.py test tests/unit/test_theorem_ledger.py
```

5. Retag to `EXACT — LEAN VERIFIED` only when the Lean theorem covers the English statement.
   Set `decl` to every declaration the statement needs, then ask Jev about that row before
   ruling; the answer is advisory and the ruling is yours. This sends statements
   to an external service: use existing session authorization, or obtain it before
   the request. The skill does not grant that authorization. If unavailable, record
   the pending review without inventing a verdict:


```powershell
python tools/formalpedia.py jev-coverage --rows <id>
```

   It prints a band and four probabilities: that the declarations cover the claim, that the
   claim asserts more than they state, that a declaration is narrower than the claim, and
   that one is a different result. Coverage below 0.5 (doubtful) and below 0.25 (not
   covered) means read the row and the declarations side by side before retagging; the
   highest failure mode says what to look for (see the formalpedia skill).
