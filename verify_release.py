#!/usr/bin/env python3
"""Verify every file in the immutable release manifest."""
from pathlib import Path,PurePosixPath
import hashlib,json
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
expected=set()
for row in manifest['files']:
 name=row['path'];path=PurePosixPath(name)
 assert not path.is_absolute() and '..' not in path.parts and name not in expected,name
 expected.add(name);p=ROOT/name
 assert p.is_file() and not p.is_symlink(),name
 data=p.read_bytes();assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'],name
actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and p.name!='MANIFEST.json' and '.git' not in p.relative_to(ROOT).parts}
assert actual==expected,{'unexpected':sorted(actual-expected),'missing':sorted(expected-actual)}
print('Release integrity PASS:',len(expected),'files;',sum(x['bytes'] for x in manifest['files']),'bytes.')
