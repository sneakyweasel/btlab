from pathlib import Path
import re
root=Path.cwd()
modules=['FejerKernel','FejerArc','FourierDiscrepancy','FejerBox']
lines=['import BTCalculus.FejerBox','','/-! Dependency audit for the finite Fejer box estimate and its supporting theorems. -/','']
count=0
for module in modules:
    names=re.findall(r'^theorem ([A-Za-z0-9_]+)',(root/'formal'/'BTCalculus'/f'{module}.lean').read_text(encoding='utf-8'),re.M)
    lines.extend(f'#print axioms BTCalculus.{module}.{name}' for name in names)
    count+=len(names)
(root/'formal'/'AxiomCheckFejerBox.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
print(f'Created audit of {count} theorems.')
