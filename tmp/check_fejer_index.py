from pathlib import Path
import json,subprocess
p=Path('data/research/formalpedia/index.json')
old=json.loads(subprocess.check_output(['git','-c','safe.directory=C:/Users/phili/Desktop/balanced_ternary','show','HEAD:data/research/formalpedia/index.json'],encoding='utf-8'))
new=json.loads(p.read_text(encoding='utf-8'))
print('Added modules:', sorted(set(new['modules'])-set(old['modules'])))
print('Declaration delta:', new['totals']['declarations']-old['totals']['declarations'])
