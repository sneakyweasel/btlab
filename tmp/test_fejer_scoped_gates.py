from pathlib import Path
import importlib.util,sys
root=Path.cwd()
view=root/'tmp/fejer_scoped_view'
sys.path.insert(0,str(root/'tools'))
import formalpedia as fp
fp.ROOT=view
fp.FORMAL=view/'formal'
fp.LEDGER=view/'docs/theory/theorem_ledger.json'
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod
index_test=load('scoped_index_test',root/'tests/tools/test_formalpedia.py')
index_test.test_every_committed_artifact_matches_a_fresh_build()
print('PASS: exact artifact freshness test on committed sources plus Q3')
layer_test=load('scoped_layer_test',root/'tests/research/juggler_sequence/test_layer_architecture.py')
layer_test.JUGGLER_DIR=view/'formal/Problems/Juggler'
layer_test.test_every_juggler_source_has_an_explicit_inventory_role()
print('PASS: exact Juggler inventory test on committed sources plus Q3')
