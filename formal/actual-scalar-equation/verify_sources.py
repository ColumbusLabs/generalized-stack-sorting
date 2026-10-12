#!/usr/bin/env python3
"""Check source bytes and dependency closure without compiling Lean."""
from pathlib import Path
import hashlib,json,re,shutil
R=Path(__file__).resolve().parent
EXPECTED_ORIGINAL='1838e0116265d52060fcba3524da8afedef36b31cff0b8e42352c7b60fd1862d'
def verify():
 manifest=json.loads((R/'SOURCE_MANIFEST.json').read_text());policy=json.loads((R/'WARNING_POLICY.json').read_text())
 rows={r['module']:r for r in manifest['modules']};assert len(rows)==len(manifest['compile_order'])==1613
 visited={};total=0
 for name in manifest['compile_order']:
  r=rows[name];b=(R/'sources'/(name.replace('.','/')+'.lean')).read_bytes();total+=len(b)
  assert hashlib.sha256(b).hexdigest()==r['sha256'],name
  imports=[]
  for line in b.decode().splitlines():
   match=re.fullmatch(r'import\s+([\w.\s]+)',line.split('--',1)[0].strip())
   if match:imports.extend(match[1].split())
  assert imports==r['imports'],name
  custom=[x for x in imports if not any(x==p or x.startswith(p+'.') for p in ['Init','Std','Lean'])]
  identity={'source':r['sha256'],'imports':{x:visited[x] for x in custom}}
  h=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest();assert h==r['closure_sha256'],name;visited[name]=h
 assert total==97526535
 assert {x['module']:x['source_sha256'] for x in policy['exceptions']}==manifest['compile_policy']['nonfatal_warning_exceptions']
 assert rows['GeneralizedActualScalarEquation']['sha256']=='a984c72914c9a6da39c9a537d6df67d27e95338742f846cd0866d65156ef476e'
 return manifest,policy
def materialize_sources(destination,manifest):
 destination.mkdir(parents=True,exist_ok=False)
 for name in manifest['compile_order']:
  relative=name.replace('.','/')+'.lean';target=destination/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/'sources'/relative,target)
if __name__=='__main__':
 m,p=verify();print('Source integrity PASS: 1,613 modules, 97,526,535 bytes; no Lean compiler invoked.')
