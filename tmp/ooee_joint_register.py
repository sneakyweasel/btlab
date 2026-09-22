from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
NOTE = 'docs/theory/juggler_ooee_joint_parity_note.md'
MODULES = ['BTCalculus/FejerBox3', 'Problems/Juggler/OOEERootPhase',
           'Problems/Juggler/OOEESlowModes', 'Problems/Juggler/OOEEParity']
JOURNAL = '''## 2026-09-22 -- Actual OOEE joint parity and slow resonances

- **Continuation audit:** The previous turn verified the pending root and
  slow-mode bounds but did not advance the production theorem. This phase
  completes their registration and proves the actual three-guard count.
- **Target and falsifier:** Transfer the proved modes to joint OOEE parity
  on the valid P^(7/16) source window. A boundary loss or an assumed
  cancellation estimate would falsify the target. Frequencies remain fixed;
  the closed longer-fibre localization and growing-depth shortcuts stay closed.
- **Proof:** The actual last root differs from x^(9/8) by at most
  3*x^(-3/8). The pure slow sum outside C*P^(-7/16) resonance windows
  is at most (2/C)*P^(7/16)+3*pi*abs(k)*D*P^(1/16)+1. Three-coordinate
  Fejer discrepancy has error 15/sqrt(H+1)+(A_H^3+6*A_H)*E, where
  A_H=1+2*harmonic(H). Exact natural-root identities identify its half-open
  box with the actual OOEE guard, including every floor boundary. The
  final count theorem supplies all mode bounds from the proved estimates.
- **Scope:** Source-window and nonresonance conditions are explicit.
  Exact target fibres and candidate counts, poor-target inclusion,
  reciprocal tail, weighted conversion and physical cutoffs remain.
  OOEEProductionBound is not discharged, so 100/203 remains the
  unconditional Lean contagion exponent. The actual failure rate is open.
- **Decision:** **PROMOTE** the actual joint parity estimate. The next
  bounded question is the target-fibre geometry and fixed-deficit resonance
  inclusion. [Proof map](theory/juggler_ooee_joint_parity_note.md).

'''

def replace_once(text, old, new):
    if new in text:
        return text
    assert text.count(old) == 1, old[:100]
    return text.replace(old, new, 1)

def transform(path, text):
    if path == 'formal/BTCalculus.lean':
        return replace_once(text, 'import BTCalculus.FejerWeighted\n',
                            'import BTCalculus.FejerWeighted\nimport BTCalculus.FejerBox3\n')
    if path == 'formal/Problems/Juggler.lean':
        return replace_once(text, 'import Problems.Juggler.OOEEMixedModes\n',
            'import Problems.Juggler.OOEEMixedModes\nimport Problems.Juggler.OOEERootPhase\n'
            'import Problems.Juggler.OOEESlowModes\nimport Problems.Juggler.OOEEParity\n')
    if path == 'src/research/juggler_sequence/lean_paths.py':
        return replace_once(text, '    "OOEEMixedModes": JUGGLER_DIR / "OOEEMixedModes.lean",\n',
            '    "OOEEMixedModes": JUGGLER_DIR / "OOEEMixedModes.lean",\n'
            '    "OOEERootPhase": JUGGLER_DIR / "OOEERootPhase.lean",\n'
            '    "OOEESlowModes": JUGGLER_DIR / "OOEESlowModes.lean",\n'
            '    "OOEEParity": JUGGLER_DIR / "OOEEParity.lean",\n')
    if path == 'formal/README.md':
        text = replace_once(text, '- original OOEE mixed-mode cancellation',
            '- actual OOEE joint parity outside explicit slow resonance windows,\n'
            '  including the last square-root comparison, three-coordinate finite\n'
            '  Fejer discrepancy and the exact natural-map guard identity. The\n'
            '  count theorem supplies its Fourier bounds from the proved modes;\n'
            '  target-fibre geometry, resonance inclusion and the tail remain. See\n'
            '  the [proof map](../docs/theory/juggler_ooee_joint_parity_note.md);\n'
            '- original OOEE mixed-mode cancellation')
        return text.replace('included. Pure slow modes and joint discrepancy remain open.',
                            'included. The subsequent joint-parity theorem supplies slow modes\n'
                            '  outside explicit resonance windows and the actual three-guard count.')
    if path == 'docs/research_journal.md':
        return replace_once(text, '# Research journal\n\n', '# Research journal\n\n'+JOURNAL)
    if path == 'docs/problems/juggler_ooee_poor_fibres.md':
        return replace_once(text,
            'Pure slow modes, joint discrepancy and the poor-target assembly remain.',
            'The actual last-root comparison, pure slow modes outside explicit resonance\n'
            'windows, and the joint three-guard count are now kernel-checked too.\n'
            '[Joint-parity proof map](../theory/juggler_ooee_joint_parity_note.md).\n'
            'Exact fibre geometry, poor-target inclusion and the tail assembly remain.')
    if path == 'docs/theory/juggler_ooee_poor_fibre_tail_note.md':
        return replace_once(text,
            'The complete analytic argument below is not yet Lean-verified. Existing\n'
            'Lean now proves the original mixed-mode estimate through its remainder,\n'
            'carry algebra, derivative tests, complete carry correlation and actual\n'
            'differencing. Pure slow modes and the poor-target assembly are still\n'
            'required to certify this theorem.',
            'The complete analytic argument below is not yet Lean-verified. Lean now\n'
            'proves the actual mixed modes, last square-root comparison, pure slow\n'
            'bounds outside explicit resonance windows and the joint OOEE guard count.\n'
            'The [joint-parity proof map](juggler_ooee_joint_parity_note.md) states the\n'
            'finite bound and its source-window hypotheses. Exact target-fibre geometry,\n'
            'poor-target inclusion, reciprocal tail and production cutoffs remain.')
    if path == 'docs/theory/juggler_ooee_mixed_modes_note.md':
        return replace_once(text,
            '**Decision: PROMOTE.** This closes the fixed mixed-mode phase. Next are\n'
            'the actual square-root phase comparison, pure slow-mode resonance\n'
            'exclusions, and three-coordinate box discrepancy. The poor-target\n'
            'inclusion, reciprocal tail and physical production cutoffs must then\n'
            'be assembled before `OOEEProductionBound` is discharged.',
            '**Decision: PROMOTE.** This closes the fixed mixed-mode phase. The\n'
            '[subsequent joint-parity proof](juggler_ooee_joint_parity_note.md) supplies\n'
            'the actual square-root comparison, pure slow-mode resonance exclusions\n'
            'and three-coordinate discrepancy with exact OOEE guard identification.\n'
            'Target-fibre geometry, poor-target inclusion, reciprocal tail and physical\n'
            'cutoffs must still be assembled before `OOEEProductionBound` is discharged.')
    if path == 'attacks/juggler/AGENT.md':
        return replace_once(text,
            '  frequency families are included. Pure slow-mode resonance exclusions,\n'
            '  full joint discrepancy, poor-target inclusion and cutoffs remain open.',
            '  frequency families are included. The [actual joint-parity bound](../../docs/theory/juggler_ooee_joint_parity_note.md)\n'
            '  now supplies the last-root comparison, nonresonant pure slow modes,\n'
            '  three-coordinate discrepancy and exact natural-map guards in Lean.\n'
            '  Target-fibre geometry, poor-target inclusion, reciprocal tail and physical\n'
            '  cutoffs remain open.')
    if path == 'docs/juggler_branch_ledger.md':
        lines = text.splitlines(keepends=True)
        for i, line in enumerate(lines):
            if '| [Actual OOEE poor fibres]' in line:
                line = line.replace('Actual mixed modes now have', 'Actual joint parity outside explicit slow resonances is now kernel-checked, including the last square-root guard and all boundary hits. Mixed modes have')
                line = line.replace('pure slow modes, joint discrepancy, poor-target inclusion, physical cutoffs,',
                                    'target-fibre geometry, poor-target inclusion, reciprocal tail, physical cutoffs,')
                lines[i] = line
                return ''.join(lines)
        raise AssertionError(path)
    raise AssertionError(path)

SHARED = ['formal/BTCalculus.lean','formal/Problems/Juggler.lean','src/research/juggler_sequence/lean_paths.py',
          'formal/README.md','docs/research_journal.md','docs/problems/juggler_ooee_poor_fibres.md',
          'docs/theory/juggler_ooee_poor_fibre_tail_note.md','docs/theory/juggler_ooee_mixed_modes_note.md',
          'attacks/juggler/AGENT.md','docs/juggler_branch_ledger.md']

def row(id, module, statement, decl):
    return dict(id=id,tag='EXACT — HUMAN PROOF',statement=statement,
                source=('docs/problems/juggler_ooee_poor_fibres.md' if id.startswith('J-') else NOTE),lean=module+'.lean',
                decl=decl,lean_trust='kernel',tests=['tests/unit/test_theorem_ledger.py',
                'tests/research/juggler_sequence/test_layer_architecture.py','tests/tools/test_formalpedia.py'],related_conjectures=[])

ROWS = [
row('J-ooee-actual-root-phase','Problems/Juggler/OOEERootPhase',
    'Kernel-checked, advisory coverage pending. Put M(x)=floor(x^(3/2)), Y(x)=M(x)^(3/2), V(x)=floor(Y(x)), W(x)=sqrt(V(x)). For x>=1, 0<=x^(9/8)-W(x)<=3*x^(-3/8). For P>=1, a>=P, L>=0 and N<=L*P^(7/16), replacing (w/2)*x^(9/8) by (w/2)*W(x) in the phase u*Y(x)+(v/2)*x^(3/2)+(w/2)*x^(9/8) changes its sum over x=a+2*n, n<N, by at most 3*pi*abs(w)*L*P^(1/16). Every fixed finite family of integer modes (i,j,k) with i or j nonzero therefore retains a common eventual O(P^(13/32)) bound for the actual phase (i/2)*x^(3/2)+(j/2)*Y(x)+(k/2)*W(x), when its samples lie in [P,2P] and N<=L*P^(7/16). Boundaries and empty sums are included; growing frequency sets and pure slow modes are excluded.',
    ['secondFloor','actualRoot','actualPhase','actualRoot_error','actual_phase_comparison','finite_actual_mixed_modes']),
row('J-ooee-nonresonant-slow-modes','Problems/Juggler/OOEESlowModes',
    'Kernel-checked, advisory coverage pending. Let P>=1,D>=0,C>0,k real and natural N. Suppose every sample a+2*n, n<N, lies in [P,P+D*P^(7/16)], C>=(9/32)*D*abs(k), and abs(k*(9/8)*P^(1/8)-z)>=C*P^(-7/16) for every integer z. With W(x)=sqrt(floor(floor(x^(3/2))^(3/2))), the norm of sum_(n<N) e((k/2)*W(a+2*n)) is at most (2/C)*P^(7/16)+3*pi*abs(k)*D*P^(1/16)+1. Both signs and actual sampled endpoints are included. Substituting P=m^(16/9), m>=1, gives slope (9/8)*m^(2/9), window length D*m^(7/9), resonance width C*m^(-7/9) and root-error term 3*pi*abs(k)*D*m^(1/9). The nonresonance condition is explicit, not proved for every target.',
    ['slowSlope','Nonresonant','slope_variation','slope_integer_band','actual_slow_samples','target_slow_samples']),
row('BTA-finite-three-coordinate-fejer-discrepancy','BTCalculus/FejerBox3',
    'Kernel-checked, advisory coverage pending. For N>0 samples in the product of three unit circles, integer H>=3 and E>=0, suppose the norm of every nonzero normalized Fourier mode with abs(i),abs(j),abs(k)<=H is at most E. For a<=b<=a+1, c<=d<=c+1, e<=f<=e+1, the count in the corresponding product of half-open circular arcs divided by N differs from (b-a)*(d-c)*(f-e) by at most 15/sqrt(H+1)+(A_H^3+6*A_H)*E, where A_H=1+2*harmonic(H). The actual Fejer smoothings, finite expansion and coordinate L1 errors prove this bound, including wrapped, empty and full arcs and sample boundary hits.',
    ['Point','mode','smooth','smooth_expansion','smooth_average_bound','product_difference','finite_box_discrepancy']),
row('J-ooee-actual-joint-parity','Problems/Juggler/OOEEParity',
    'Kernel-checked, advisory coverage pending. For every fixed integer H>=3 and real D>=0 there are B>0 and P0 such that for P>=P0, odd natural a, natural N>0 and real C>0, if all a+2*n (n<N) lie in [P,2P] and [P,P+D*P^(7/16)], N<=D*P^(7/16), C>=(9/32)*D*H, and abs(k*(9/8)*P^(1/8)-z)>=C*P^(-7/16) for all integers 0<abs(k)<=H and z, then abs(count_(n<N)(ooeeGuard(a+2*n))/N-1/8)<=15/sqrt(H+1)+(A_H^3+6*A_H)*(B*P^(13/32)+(2/C)*P^(7/16)+3*pi*H*D*P^(1/16)+1)/N, with A_H=1+2*harmonic(H). The guard is the actual natural Juggler OOEE itinerary. The half-open box identity and every Fourier bound are proved, including floor boundaries. Constants B,P0 are independent of P,a,N,C. Exact target-fibre geometry, poor-target inclusion, reciprocal tail, physical cutoffs and OOEEProductionBound are not supplied.',
    ['point','point_guards','mode_phase','actual_guard_discrepancy','nonresonant_guard_discrepancy'])]

def append_rows(text):
    known = {r['id']:r for r in json.loads(text)}
    for row in ROWS:
        if row['id'] in known and known[row['id']] != row:
            fmt=lambda x:'\n'.join(' '+line for line in json.dumps(x,ensure_ascii=False,indent=1).splitlines())
            old=fmt(known[row['id']])
            assert text.count(old)==1
            text=text.replace(old,fmt(row),1)
    missing = [r for r in ROWS if r['id'] not in known]
    if not missing:
        return text
    assert text.rstrip().endswith(']')
    tail = ',\n'.join('\n'.join(' '+line for line in json.dumps(r,ensure_ascii=False,indent=1).splitlines()) for r in missing)
    return text.rstrip()[:-1].rstrip()+',\n'+tail+'\n]\n'

if __name__ == '__main__':
    for p in SHARED:
        path=ROOT/p
        old=path.read_text(encoding='utf-8')
        new=transform(p,old)
        if new!=old: path.write_text(new,encoding='utf-8')
    p=ROOT/'docs/theory/theorem_ledger.json'
    p.write_text(append_rows(p.read_text(encoding='utf-8')),encoding='utf-8')
    lines=['import Problems.Juggler.OOEEParity','']
    for module in MODULES:
        source=(ROOT/'formal'/f'{module}.lean').read_text(encoding='utf-8')
        for name in re.findall(r'^theorem\s+(\w+)',source,re.M):
            lines.append('#print axioms '+module.replace('/','.')+'.'+name)
    (ROOT/'formal/AxiomCheckOOEEJointParity.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    print('Registered rows:',len(ROWS),'audit declarations:',len(lines)-2)
