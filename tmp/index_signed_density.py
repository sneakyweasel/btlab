from pathlib import Path
root=Path(__file__).resolve().parents[1]
source=(root/'tmp/index_preimage_domain.py').read_text(encoding='utf-8')
start=source.index("for rel in ('formal/Problems.lean'")
end=source.index('    target = snapshot / rel', start)
modules=['PreimageGrowth','PreimageCertificate','PreimageDensity','PreimageWeights12',
         'PreimageCheck12Part0','PreimageCheck12Part1','PreimageCheck12Part2','PreimageCheck12Part3',
         'PreimageCertificate12']
paths=['formal/Problems.lean']+[f'formal/Problems/Collatz/{m}.lean' for m in modules]
source=source[:start]+'for rel in '+repr(tuple(paths))+':\n'+source[end:]
source=source.replace('the three scoped Lean files', 'the scoped signed-density Lean files')
exec(compile(source,str(root/'tmp/index_preimage_domain.py'),'exec'), {'__file__':str(root/'tmp/index_preimage_domain.py')})
