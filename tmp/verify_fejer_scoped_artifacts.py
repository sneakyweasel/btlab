from pathlib import Path
import importlib.util,json,shutil,zipfile
root=Path.cwd()
view=root/'tmp'/'fejer_scoped_view'
assert not view.exists()
view.mkdir()
with zipfile.ZipFile(root/'tmp/fejer_scoped_base.zip') as z:
    z.extractall(view)
owned=['formal/BTCalculus.lean','formal/BTCalculus/FejerKernel.lean','formal/BTCalculus/FejerArc.lean','formal/BTCalculus/FourierDiscrepancy.lean','formal/BTCalculus/FejerBox.lean','docs/theory/theorem_ledger.json']
for name in owned:
    dest=view/name
    dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(root/name,dest)
spec=importlib.util.spec_from_file_location('scoped_fp',root/'tools/formalpedia.py')
fp=importlib.util.module_from_spec(spec)
spec.loader.exec_module(fp)
fp.ROOT=view
fp.FORMAL=view/'formal'
fp.LEDGER=view/'docs/theory/theorem_ledger.json'
index=fp.build()
ledger=json.loads(fp.LEDGER.read_text(encoding='utf-8'))
artifacts=[
 ('data/research/formalpedia/index.json',fp.render(index)),
 ('data/research/formalpedia/decl_proposals.json',fp.render(fp.propose(index,ledger))),
 ('data/research/formalpedia/dag.json',fp.render(fp.dag(index,ledger))),
 ('docs/research/formalpedia_decl_review.md',fp.review_digest(index,ledger)),
 ('docs/research/formalpedia_coverage_review.md',fp.coverage_digest(index,ledger)),
]
for name,fresh in artifacts:
    actual=(root/name).read_text(encoding='utf-8')
    assert actual.replace('\r\n','\n')==fresh.replace('\r\n','\n'),name
    print('Scoped artifact verified:',name)
assert 'Problems.Juggler.OOEEFourierModes' not in index['modules']
print('All artifacts match committed sources plus the Q3 changes; concurrent OOEE draft excluded.')
