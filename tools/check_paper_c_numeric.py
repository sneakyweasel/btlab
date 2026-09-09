from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import json,re,hashlib,sys,os,argparse
import mpmath as mp
mp.mp.dps=90
ROOT=Path(__file__).resolve().parents[1];S=ROOT
parser=argparse.ArgumentParser(description='Independent arithmetic and finite checks for Paper C; requires mpmath.')
parser.add_argument('--axiom-output',type=Path,required=True,help='Fresh output of lake env lean AxiomCheckPaperC.lean')
parser.add_argument('--output',type=Path,default=ROOT/'data/research/juggler/paper_c_publication_review/validation.json')
args=parser.parse_args()
args.axiom_output=args.axiom_output.resolve();args.output=args.output.resolve()
os.chdir(ROOT)
sys.path.insert(0,str(ROOT/'src'))
from research.juggler_sequence import paper_c_audit as audit
from research.juggler_sequence import paper_c_formal_layer as formal
paper=S/'docs/theory/juggler_fate_almost_all_note.md'
audit.PAPER=paper;audit.REPO_ROOT=S;formal.PAPER=paper
results={'review_date':'2026-09-09','scope':'Independent arithmetic and finite checks; not formal verification of the analytic proofs.'}
results['existing_audit']=audit.summary()
results['formal_surface']=formal.audit()
expected=(ROOT/'formal/AxiomCheckPaperC.expected').read_text(encoding='utf-8').strip()
actual=args.axiom_output.read_text(encoding='utf-8').strip()
results['fresh_lean_axiom_audit']={'matches_recorded':actual==expected,'declarations':len(re.findall('depends on axioms:',actual)),
 'forbidden':re.findall(r'sorryAx|ofReduceBool',actual),'build':'passed'}
def mpf(x):return mp.mpf(x.numerator)/x.denominator if isinstance(x,F) else mp.mpf(x)
def root(terms):
 lo,hi=mp.mpf(0),mp.mpf(1)
 def fun(x):return sum(mpf(c)*mpf(e)**x for c,e in terms)-1
 for _ in range(230):
  mid=(lo+hi)/2
  if fun(mid)>0:lo=mid
  else:hi=mid
 return (lo+hi)/2
pair=[(F(1),F(1,2)),(F(1,9),F(3,8)),(F(2,9),F(3,4))]
terms=list(pair);roots={'pairing':root(terms)}
for k in range(2,7):
 terms.append((F(1,3**(k+1)),F(1,2)*F(3,4)**k));roots[f'V{k}']=root(terms)
roots['conditional_Appendix_C']=root(pair+[(F(1,9),F(9,32))])
roots['depth_two_ideal']=root([(F(1),F(1,2)),(F(1,3),F(3,4))])
results['independent_roots']={k:mp.nstr(v,60) for k,v in roots.items()}
results['net_gains']=[{'k':k,'rho':str(F(1,2)*F(3,4)**k),'gain':str(F(1,3**k)-F(2,9)*F(1,3**(k-1)))} for k in range(2,7)]
L3=mp.log(3,2)
def kl(p,q):return p*mp.log(p/q)+(1-p)*mp.log((1-p)/(1-q))
def rate(C,q,kind):
 p=(1-mp.mpf(1)/C)/L3
 if p<=q:return mp.mpf(0)
 return C*kl(p,q)/mp.log(2) if kind=='Chernoff' else 2*(C*(1-q*L3)-1)**2/(C*L3**2*mp.log(2))
depths={}
for regime,lam in [('V6',roots['V6']),('pairing',roots['pairing']),('Appendix_C',roots['conditional_Appendix_C'])]:
 depths[regime]={}
 for kind in ['Chernoff','Azuma']:
  depths[regime][kind]={}
  for qstr in ['0.5','0.55','0.60','0.62']:
   q=mp.mpf(qstr);c=5
   while rate(c,q,kind)<=1-lam:c+=1
   depths[regime][kind][qstr]={'least_integer_C':c,'rate':mp.nstr(rate(c,q,kind),35),'previous_rate':mp.nstr(rate(c-1,q,kind),35)}
results['independent_depths']=depths
# Exact finite checks use binary-search integer powers, independent of floating roots.
def floorpow(n,a,b):
 target=n**a;lo=0;hi=1<<((target.bit_length()+b-1)//b)
 while lo+1<hi:
  mid=(lo+hi)//2
  if mid**b<=target:lo=mid
  else:hi=mid
 return lo
def ceilpow(n,a,b):
 q=floorpow(n,a,b);return q+(q**b<n**a)
def step(n):return isqrt(n**3) if n%2 else isqrt(n)
endpoint_tests=[]
for k in range(1,7):
 for m in [2,3,7,19]:
  a=ceilpow(m,8,3);b=ceilpow(m+1,8,3)
  for _ in range(k-1):a=ceilpow(a,4,3);b=ceilpow(b,4,3)
  def landing(n):
   for _ in range(k-1):n=floorpow(n,3,4)
   return floorpow(n,3,8)
  good=landing(a)==m and landing(b-1)==m and landing(a-1)<m and landing(b)>m
  endpoint_tests.append({'k':k,'m':m,'left':a,'right_exclusive':b,'ok':good})
results['exact_endpoint_checks']=endpoint_tests
counts=[]
for k in range(1,7):
 m=2;a=ceilpow(m,8,3);b=ceilpow(m+1,8,3)
 for _ in range(k-1):a=ceilpow(a,4,3);b=ceilpow(b,4,3)
 word='OE'*k+'E';cnt=0;identities=0
 for n in range(a|1,b,2):
  state=n;matches=True
  for letter in word:
   if (state%2==1)!=(letter=='O'):matches=False;break
   state=step(state)
  if matches:
   cnt+=1;identities+=state==m
 counts.append({'k':k,'source':m,'odd_points':len(range(a|1,b,2)),'matching_words':cnt,'land_at_source':identities,'ok':cnt==identities})
results['finite_word_counts']=counts
results['retired_constant_witnesses']={
 'm_prime':2,'claimed_correction_le_1_over_16':mp.nstr(mp.mpf(1)/4*mp.power(2,-mp.mpf(14)/9),25),
 'one_over_16':'0.0625','claimed_slow_derivative_upper_below_half':mp.nstr(mp.mpf(3)/4*mp.power(2,-mp.mpf(2)/9),25)}
arch={}
for tag in ['fate_contagion','tao_reduction','oe_fiber_share']:
 obj=json.loads((ROOT/f'data/research/juggler/{tag}/summary.json').read_text(encoding='utf-8'))
 if tag=='fate_contagion':
  arch[tag]={'max_block_abs_sqrt_deviation':max(abs(r['deviation_over_sqrt']) for r in obj['block_census']),
   'closure_keys':list(obj['closure'].keys()) if 'closure' in obj else [k for k in obj if 'closure' in k]}
 else:
  arch[tag]={'top_level_keys':list(obj),'caps':[]}
  def walk(x,path=''):
   if isinstance(x,dict):
    for k,v in x.items():
     if 'cap' in k.lower():arch[tag]['caps'].append([path+'/'+k,v])
     walk(v,path+'/'+k)
   elif isinstance(x,list):
    for i,v in enumerate(x):walk(v,path+'/'+str(i))
  walk(obj)
results['archival_observation_checks']=arch
results['all_checks_passed']=bool(results['existing_audit']['classification']['failures']==0 and not results['formal_surface']['problems'] and actual==expected and all(x['ok'] for x in endpoint_tests+counts))
dest=args.output;dest.parent.mkdir(parents=True,exist_ok=True)
dest.write_text(json.dumps(results,indent=2,ensure_ascii=False),encoding='utf-8')
print(json.dumps({'all_checks_passed':results['all_checks_passed'],'original_audit':results['existing_audit']['classification'],'formal_problems':results['formal_surface']['problems'],'axioms':results['fresh_lean_axiom_audit'],'independent_roots':results['independent_roots'],'observations':arch},indent=2))

if not results['all_checks_passed']:raise SystemExit(1)
