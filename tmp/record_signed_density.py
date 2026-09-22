import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
path = root / 'docs/theory/theorem_ledger.json'
text = path.read_text(encoding='utf-8')
def edit_row(identifier, fn):
    global text
    pos = text.index('"id": ' + json.dumps(identifier))
    start = text.rfind('{', 0, pos)
    row, length = json.JSONDecoder().raw_decode(text[start:])
    fn(row)
    lines = json.dumps(row, ensure_ascii=False, indent=1).splitlines()
    replacement = lines[0] + '\n' + '\n'.join(' '+line for line in lines[1:])
    text = text[:start] + replacement + text[start+length:]

def density(row):
    row.update(
        tag='EXACT — HUMAN PROOF',
        statement='For the positive natural 3n-1 shortcut map g, every positive target a with a mod 3 nonzero admits a natural cutoff X_0 such that for every natural X>=X_0, X^21<=N(a,X)^25. Here N(a,X) counts positive starts n<=X whose orbit reaches a with every intermediate state at most X. The ordinary positive ancestor count pi(a,X), with no intermediate-height restriction, also satisfies X^21<=pi(a,X)^25; equivalently there are at least X^(21/25)=X^0.84 ancestors up to every sufficiently large natural X. This includes cycle targets and assumes no exhaustive classification of cycles. The proof uses actual signed strict-grid recurrences, a closed root domain, well-founded root induction, and an independently generated level-12 certificate with 177147 positive integer weights and rate 5059/5000. Every row, the exact comparison 2^21*5000^1250<5059^1250, and cutoff interpolation are kernel-checked. The former proof by automatic residue negation remains withdrawn; the new proof retains the signed height correction. M. Sharpe\'s MIT root-induction method is attributed. No Juggler termination or divergent harmonic-mass estimate follows. Ledger label awaits advisory statement-coverage review.',
        lean='Problems/Collatz/PreimageCertificate12.lean',
        decl=['all_rows', 'weight_system', 'target_growth', 'rate_gap', 'density_21_25', 'ancestor_density_21_25'],
        lean_trust='kernel')
edit_row('J-kl-preimage-density-transposes-to-3n-1', density)
edit_row('J-signed-preimage-grid-counting', lambda row: row.update(statement=row['statement'].replace(
    'the growth induction and numerical certificate remain unproved here. No density exponent or termination theorem follows yet.',
    'the growth induction and full level-12 certificate have now been completed in PreimageCertificate12.lean, proving the eventual exponent 21/25. The pointwise recurrences alone do not supply that conclusion, and no termination theorem follows.')))
edit_row('J-signed-preimage-closed-root-domain', lambda row: row.update(statement=row['statement'].replace(
    'The growth induction and a checked numerical growth certificate remain open; no density exponent or termination result is asserted.',
    'The subsequent PreimageCertificate12.lean completes the growth induction and checked certificate, proving the eventual exponent 21/25. This domain lemma alone is not that counting bound, and no termination result is asserted.')))
json.loads(text)
path.write_text(text,encoding='utf-8')

replacements = {
 'literature/sharpe-2026-collatz-grid-root-induction.json': (
   'The growth induction and its checked certificate remain open. No signed density exponent or Juggler termination theorem is claimed.',
   'The signed growth induction is now compiled in PreimageGrowth.lean. An independently generated 177147-row level-12 integer certificate at rate 5059/5000 has been checked entirely by the Lean kernel. PreimageCertificate12.ancestor_density_21_25 proves the eventual X^21<=ancestorCount(a,X)^25 bound for every positive target prime to 3, after exact dyadic interpolation. The external advertised large certificates have still not been independently audited here. No Juggler termination theorem follows.'),
 'literature/krasikov-lagarias-2003-difference-inequalities.json': (
   'the growth induction and its checked certificate remain open. No new density or termination theorem is attributed to this audit.',
   'the signed growth induction and an independent 177147-row integer certificate are now kernel-checked. PreimageCertificate12.ancestor_density_21_25 proves the eventual exponent 21/25 for every positive target prime to 3. This completes the separate strict-grid repair, not the original residue-only inference. No Juggler termination theorem follows.'),
}
for rel, (old,new) in replacements.items():
    p = root/rel
    s = p.read_text(encoding='utf-8')
    assert s.count(old)==1, rel
    s = s.replace(old,new)
    if 'krasikov-lagarias' in rel:
        s = s.replace('The density transfer is now unproved in this branch; its asymptotic conclusion is not refuted.',
                      'That audit returned the density transfer to unproved status without refuting its asymptotic conclusion; the completed repair is recorded below.')
    p.write_text(s,encoding='utf-8')

p = root/'docs/juggler_branch_ledger.md'
s = p.read_text(encoding='utf-8')
lines=s.splitlines()
for i,line in enumerate(lines):
    if line.startswith('| Signed Collatz preimages |'):
        lines[i]='| Signed Collatz preimages | [Checked preimage density](problems/juggler_negative_preimage_density.md) | PROMOTE | `PreimageCertificate12.ancestor_density_21_25`: for every positive unit target, eventually X^21<=ancestorCount(a,X)^25 | Actual signed recurrences, closed domain, root induction, all 177147 integer certificate rows, and cutoff interpolation are kernel-checked; the original residue-only argument remains withdrawn | Signed exponent 21/25 established for all large natural cutoffs, including cycle targets; no Juggler termination bound follows |'
p.write_text('\n'.join(lines)+'\n',encoding='utf-8')

p = root/'docs/research_journal.md'
s = p.read_text(encoding='utf-8')
entry='''## 2026-09-22 -- The signed ancestor-density exponent 21/25 is kernel-checked

- **Question:** Do the exact signed grid recurrences admit a growth
  certificate, and does it imply a bound for every sufficiently large cutoff?
- **Certificate:** An independent damped Collatz–Wielandt iteration found
  a positive level-12 table at p/q=5059/5000 after 62 iterations. All
  177147 inequalities pass exact integer checking. Weights range from
  7307142888 to 10^12. Four Lean modules check every row in blocks of 256;
  a balanced lookup tree and small data shards bound reduction cost.
  No compiler-trusted decision tactic is used. The certificate data and
  `tools/generate_signed_grid_certificate.py --check` reproduce the five
  generated files; the solver is outside the trusted proof.
- **Proof:** `PreimageGrowth.growth_root` adapts M. Sharpe's attributed
  root-induction method to the actual signed recurrences and closed domain.
  `PreimageCertificate.weightSystem_of_rows` selects the actual child's
  residue lift. `PreimageDensity.density_of_weight_system` interpolates
  dyadic cutoffs and absorbs fixed constants using a strict rational rate.
  The kernel checks 2^21*5000^1250<5059^1250.
- **Result:** `PreimageCertificate12.density_21_25` proves, for every
  positive target a prime to 3, the existence of X_0 such that every
  natural X>=X_0 satisfies X^21<=N(a,X)^25 for the capped inverse tree.
  `ancestor_density_21_25` proves the same for ordinary positive ancestors.
  This includes cycle targets and assumes no exhaustive cycle classification.
- **Decision:** **PROMOTE** the complete signed density theorem. The earlier
  automatic residue-only proof remains withdrawn. The result supplies no
  new Juggler pressure estimate, divergent harmonic-mass estimate, universal
  termination theorem, or infinite escape trajectory. Papers C and D are
  unchanged. No independent priority claim is made for the grid method.
- **Validation:** Full `lake build` passes (9040 jobs); all 21 audited
  declarations have only standard Lean dependencies. All four finite check
  modules compiled, and the independent verifier rejects corrupted positive
  weights as well as invalid dimensions and zero weights.
- **Coverage:** The existing density row is now `EXACT — HUMAN PROOF`,
  with the exact Lean declarations and kernel trust recorded. The advisory
  English-statement check remains pending; no new theorem data was sent out.

'''
assert s.startswith('# Research journal\n\n')
p.write_text('# Research journal\n\n'+entry+s[len('# Research journal\n\n'):],encoding='utf-8')
