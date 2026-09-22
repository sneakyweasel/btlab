import json
from pathlib import Path

p = Path('docs/theory/theorem_ledger.json')
text = p.read_text(encoding='utf-8')
key = 'J-paper-c-ceiling-is-the-collatz-walk-mgf'
start = text.index(' {\n  "id": "' + key + '",')
old, length = json.JSONDecoder().raw_decode(text[start + 1:])
old.update({
    'lean': 'Problems/Juggler/CollatzMoments.lean',
    'decl': ['fairWeight', 'multiplier', 'idealCoeff', 'coefficient_shift',
             'fair_children', 'tilted_children', 'fixed_depth_fair', 'fixed_depth_moment'],
    'lean_trust': 'kernel',
    'statement': "For each finite parity word w, define p_w=2^(-|w|), rho_w=3^(oddCount w)/2^|w|, and c_w=3^(-oddCount w). For every real s, c_w*rho_w^s=p_w*rho_w^(s-1). At every fixed depth d, summing over all binary words of length d gives sum p_w=1 and sum p_w*rho_w=1. The fair and tilted child weights each sum to their parent's weight, so finite leaf expansions preserve both totals. These are word identities, not arithmetic counting estimates for Juggler starts. Correction of 22 September 2026: the previous complete-prefix-free wording did not distinguish bounded trees from unbounded stopping. Completeness alone does not preserve the second moment identity: J-collatz-complete-stopping-loses-moment supplies a kernel-checked counterexample. The coefficient shift and Proposition 5.12's ideal-model root at one remain valid. The stale attribution of the entire gap to a parity shortfall is removed: Paper C's printed individual coefficients already equal the ideal, while overlap and truncation affect their assembly. Compiled declarations and an 18-declaration dependency audit are recorded; the ledger tag awaits advisory coverage review."
})
new = {
    'id': 'J-collatz-complete-stopping-loses-moment',
    'tag': 'EXACT — HUMAN PROOF',
    'source': 'docs/problems/juggler_collatz_bridge.md',
    'lean': 'Problems/Juggler/CollatzMoments.lean',
    'decl': ['certMass', 'tiltedCertMass', 'certMass_eq_sum',
             'certificate_prefix_free', 'certificate_mass_partition',
             'certificate_hasSum', 'tilted_summable', 'stopped_moment_le',
             'complete_family_moment_loss'],
    'lean_trust': 'kernel',
    'tests': ['tests/research/juggler_sequence/test_collatz_bridge.py'],
    'related_conjectures': [],
    'statement': "The family of all minimal exponent-descent certificate words is prefix-free: if two certificates are in the prefix relation, they are equal. Grouping by positive word length, its fair mass has sum one: HasSum certMass 1, where certMass d=M_(d+1)/2^(d+1). This follows from the exact partition sum_(d<D) certMass d+N_D/2^D=1 and the existing unconditional word-survivor decay. Its tilted mass, the sum of 2^(-|w|)*rho_w with rho_w=3^(oddCount w)/2^|w|, is summable and at most 3/4, hence not one. Every terminal multiplier is below one; the certificate E has fair mass 1/2 but tilted mass 1/4, and the remaining fair mass is 1/2. Thus Kraft completeness alone does not justify the first multiplier-moment identity at unbounded stopping. This is a counterexample to the former unrestricted second-root sentence in Paper C Section 5.7, not to its coefficient shift, Proposition 5.12, or a termination theorem. The compiled theorem complete_family_moment_loss packages the prefix-free property and both sums. Ledger label awaits advisory coverage review."
}
def render(row):
    return ' ' + json.dumps(row, ensure_ascii=False, indent=1).replace('\n', '\n ')
text = text[:start] + render(old) + ',\n' + render(new) + text[start + 1 + length:]
json.loads(text)
p.write_text(text, encoding='utf-8')
