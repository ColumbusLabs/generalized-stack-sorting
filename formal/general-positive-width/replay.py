#!/usr/bin/env python3
"""Verify exact source bytes, or rebuild every project module from source on Linux.
No existing project objects are imported. Official pinned library caches are trusted.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
from resource_guard import guarded_run
ROOT = Path(__file__).resolve().parent
MANIFEST_SHA256 = '31906d3f4f2cf962b74e0506029aa71b353a6b69c39333abf998761ebe27eed7'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def code_only(text):
    """Remove nested comments and strings, preserving line boundaries."""
    result = []; i = 0; depth = 0; string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else:
                if text[i] == '\n': result.append('\n')
                i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; i += 1
            else:
                if text[i] == '\n': result.append('\n')
                i += 1
        elif pair == '/-': depth = 1; i += 2; result.append(' ')
        elif pair == '--':
            end = text.find('\n', i); i = len(text) if end < 0 else end
        elif text[i] == '"': string = True; i += 1; result.append(' ')
        else: result.append(text[i]); i += 1
    if depth or string: raise ValueError('Unterminated Lean comment or string')
    return ''.join(result)


def imports(text):
    return [name for line in re.findall(r'^\s*import\s+([^\n]+)', code_only(text), re.M) for name in line.split()]


def source_path(root, relative):
    # Only this package, or the explicitly shared sibling source certificate.
    if not (relative.startswith('sources/') or relative.startswith('controls/') or
            relative.startswith('../actual-scalar-equation/sources/')):
        raise ValueError('Unexpected source location: ' + relative)
    path = root / relative
    if path.is_symlink() or not path.is_file(): raise ValueError('Missing or symlink source: ' + relative)
    boundary = root.parent.resolve()
    if not path.resolve().is_relative_to(boundary): raise ValueError('Source outside formal directory')
    return path


def verify(root=ROOT):
    root = Path(root)
    if sha256(root/'SOURCE_MANIFEST.json') != MANIFEST_SHA256:
        raise ValueError('Source manifest digest mismatch')
    manifest = json.loads((root/'SOURCE_MANIFEST.json').read_text())
    rows = manifest['modules']; names = [r['module'] for r in rows]
    if len(names) != manifest['module_count'] or len(set(names)) != len(names):
        raise ValueError('Duplicate or missing modules')
    seen = set(); external = set()
    for row in rows + manifest['controls']:
        path = source_path(root, row['path'])
        if sha256(path) != row['sha256'] or path.stat().st_size != row['bytes']:
            raise ValueError('Source bytes changed: ' + row['module'])
        text = path.read_text()
        if imports(text) != row['imports']: raise ValueError('Import list changed: ' + row['module'])
        if re.search(r'\b(sorry|admit|axiom|constant|native_decide|unsafe)\b', code_only(text)):
            raise ValueError('Forbidden declaration/proof token: ' + row['module'])
        for dep in row['imports']:
            if dep in names:
                if dep not in seen: raise ValueError('Invalid dependency order: ' + row['module'] + ':' + dep)
            elif dep.split('.')[0] not in {'Init', 'Std', 'Lean', 'Mathlib'}:
                raise ValueError('Missing project import: ' + dep)
            else: external.add(dep)
        if row in rows: seen.add(row['module'])
    if sorted(external) != manifest['external_imports']: raise ValueError('External import inventory mismatch')
    # Detect unmanifested source files; shared sibling modules are separately pinned above.
    expected = {r['path'] for r in rows + manifest['controls'] if not r['path'].startswith('../')}
    actual = {str(p.relative_to(root)) for folder in ('sources', 'controls') for p in (root/folder).rglob('*.lean')}
    if actual != expected: raise ValueError('Unmanifested or missing local source file')
    return manifest


def verify_files(root=ROOT):
    inventory = json.loads((Path(root)/'FILE_MANIFEST.json').read_text())
    actual = {str(p.relative_to(root)) for p in Path(root).rglob('*') if p.is_file()
              and p.name != 'FILE_MANIFEST.json' and '__pycache__' not in p.parts}
    if actual != set(inventory): raise ValueError('Package file membership changed')
    for name, row in inventory.items():
        p = Path(root)/name
        if p.is_symlink() or sha256(p) != row['sha256'] or p.stat().st_size != row['bytes']:
            raise ValueError('Package file changed: ' + name)


def verify_toolchain(lean, mathlib, manifest):
    pins = json.loads((ROOT/'TOOLCHAIN.json').read_text())
    lean = Path(lean).resolve(); prefix = lean.parent.parent; mathlib = Path(mathlib).resolve()
    for relative, digest in pins['lean_linux_files'].items():
        if sha256(prefix/relative) != digest: raise ValueError('Compiler file mismatch: ' + relative)
    if lean != prefix/'bin/lean': raise ValueError('Supply the official bin/lean executable')
    def git(directory, *args):
        return subprocess.check_output(['git', '-C', str(directory), *args], text=True).strip()
    if git(mathlib, 'rev-parse', 'HEAD') != pins['mathlib_revision'] or git(mathlib, 'status', '--porcelain'):
        raise ValueError('Mathlib revision or working-tree mismatch')
    if sha256(mathlib/'lake-manifest.json') != pins['mathlib_lake_manifest_sha256']:
        raise ValueError('Mathlib dependency manifest changed')
    if (mathlib/'lean-toolchain').read_text().strip() != pins['lean_toolchain']:
        raise ValueError('Mathlib Lean toolchain mismatch')
    paths = []
    package_rows = json.loads((mathlib/'lake-manifest.json').read_text())['packages']
    expected_packages = {p['name']:p for p in pins['packages']}
    if set(expected_packages) != {p['name'] for p in package_rows}: raise ValueError('Package membership mismatch')
    for row in package_rows:
        p = mathlib/'.lake/packages'/row['name']; expected = expected_packages[row['name']]
        if row['type'] != 'git' or row['rev'] != expected['revision'] or row['url'] != expected['url']:
            raise ValueError('Package manifest revision mismatch: ' + row['name'])
        if git(p, 'rev-parse', 'HEAD') != row['rev'] or git(p, 'status', '--porcelain'):
            raise ValueError('Package revision or working-tree mismatch: ' + row['name'])
        lib = p/'.lake/build/lib/lean'
        if lib.is_dir(): paths.append(lib)
    paths.append(mathlib/'.lake/build/lib/lean')
    builtin = prefix/'lib/lean'
    for row in manifest['modules'] + manifest['controls']:
        for lib in paths + [builtin]:
            if (lib/(row['module']+'.olean')).exists(): raise ValueError('Project object collision in library path')
    for dep in manifest['external_imports']:
        rel = Path(*dep.split('.')).with_suffix('.olean')
        if not any((p/rel).is_file() for p in paths+[builtin]): raise ValueError('Missing official library cache: ' + dep)
    return lean, paths


def replay(args, manifest):
    lean, libs = verify_toolchain(args.lean, args.mathlib, manifest)
    out = Path(args.output).resolve()
    if out.exists(): raise ValueError('Output directory must not already exist')
    if out.is_relative_to(ROOT): raise ValueError('Output must be outside the certificate directory')
    if shutil.disk_usage(out.parent).free < 768*1024**2: raise ValueError('Require 768 MiB free before replay')
    out.mkdir(); build=out/'build'; build.mkdir(); logs=out/'captures'; logs.mkdir()
    for row in manifest['modules'] + manifest['controls']:
        shutil.copyfile(source_path(ROOT, row['path']), build/(row['module']+'.lean'))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,[build]+libs)), NO_COLOR='1', PYTHONDONTWRITEBYTECODE='1')
    for key in ('LEAN_SYSROOT', 'LEAN_OPTS', 'LEAN_SRC_PATH'): env.pop(key, None)
    records=[]; objects={}; audits={}
    allrows = manifest['modules'] + manifest['controls']
    rows = {r['module']:r for r in allrows}
    def check_stability():
        for name,row in rows.items():
            if sha256(build/(name+'.lean')) != row['sha256']: raise ValueError('Copied source changed: '+name)
        for name,digest in objects.items():
            if sha256(build/(name+'.olean')) != digest: raise ValueError('Built object changed: '+name)
    config = {'source_manifest_sha256':MANIFEST_SHA256, 'replay_sha256':sha256(__file__),
              'resource_guard_sha256':sha256(ROOT/'resource_guard.py'), 'toolchain_sha256':sha256(ROOT/'TOOLCHAIN.json'),
              'project_object_reuse':False, 'official_library_caches_trusted':True, 'profile':manifest['resource_profile']}
    (out/'CONFIGURATION.json').write_text(json.dumps(config,indent=2)+'\n')
    for row in allrows:
        name=row['module']; target=build/(name+'.olean'); negative=row.get('expect')=='reject'
        if target.exists(): raise ValueError('Unexpected existing project object: '+name)
        if sha256(build/(name+'.lean')) != row['sha256']: raise ValueError('Source mutation: '+name)
        dep_objects={}
        for dep in row['imports']:
            if dep in rows:
                digest=sha256(build/(dep+'.olean'))
                if digest != objects[dep] or sha256(build/(dep+'.lean')) != rows[dep]['sha256']:
                    raise ValueError('Imported project input changed: '+dep)
                dep_objects[dep]=digest
        expected=row['warnings']
        profile=row.get('resource_profile',manifest['resource_profile'])
        cmd=[str(lean),'-j1']
        if profile['internal_lean_heap_limit'] is not None: cmd.append('-M'+str(profile['internal_lean_heap_limit']))
        cmd+=['-DwarningAsError='+str(not bool(expected)).lower(),'-o',name+'.olean',name+'.lean']
        code,stdout,stderr,guard=guarded_run(cmd,build,env,logs,name,profile)
        output=stdout+stderr; actual=[l for l in output.splitlines() if ': warning:' in l]
        axiom_rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)
        axiom_ok=True
        for endpoint,body in axiom_rows:
            used={s.strip() for s in body.split(',') if s.strip()}
            if not used <= ALLOWED_AXIOMS: axiom_ok=False
            audits[endpoint]=sorted(used)
        for endpoint in re.findall(r"'([^']+)' does not depend on any axioms",output): audits[endpoint]=[]
        clean=not guard['signals'] and not guard['remaining_members'] and actual==expected and 'sorryAx' not in output and axiom_ok
        if negative:
            intended=any(s.lower() in output.lower() for s in row['required_diagnostics'])
            bad=any(s in output.lower() for s in ['unknown identifier','unknown module','unexpected token','failed to synthesize','object file','failed to read file','excessive memory','out of memory','panic','maximum recursion','maximum number of heartbeats'])
            passed=clean and code==1 and guard['status']=='failed' and intended and not bad
        else: passed=clean and code==0 and guard['status']=='passed' and target.is_file()
        record={'module':name,'expect':'reject' if negative else 'pass','passed':passed,'source_sha256':row['sha256'],
                'object_sha256':sha256(target) if target.exists() else None,'imported_project_objects':dep_objects,
                'exit_code':code,'command':cmd,'guard':guard,'resource_profile':profile,'warnings':actual,'stdout_sha256':sha256(logs/(name+'.stdout.log')),
                'stderr_sha256':sha256(logs/(name+'.stderr.log'))}
        records.append(record); (out/'RESULTS.json').write_text(json.dumps(records,indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if not passed: raise RuntimeError('Replay case failed: '+name+'; see captured diagnostics')
        if not negative: objects[name]=record['object_sha256']
    verify(); verify_files(); verify_toolchain(args.lean,args.mathlib,manifest); check_stability()
    missing=set(manifest['required_audit_endpoints'])-set(audits)
    if missing: raise ValueError('Required endpoint axiom reports missing: '+str(sorted(missing)))
    summary={'status':'FRESH_SOURCE_REPLAY_AND_CONTROLS_PASS','project_modules':manifest['module_count'],
             'controls':len(manifest['controls']),'project_object_reuse':False,'source_manifest_sha256':MANIFEST_SHA256,
             'all_observed_axioms':sorted({a for xs in audits.values() for a in xs}),'endpoint_axiom_audits':audits,
             'trust_boundary':'Pinned official compiler and library caches; this replay is not the historical recursive dependency audit.'}
    (out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--verify-only',action='store_true'); p.add_argument('--lean'); p.add_argument('--mathlib'); p.add_argument('--output')
    args=p.parse_args(); manifest=verify(); verify_files()
    if args.verify_only:
        print('PASS: exact source bytes, complete project import closure, order, warnings, controls and package inventory; no Lean launched.'); return
    if not all((args.lean,args.mathlib,args.output)): p.error('replay requires --lean, --mathlib and --output')
    replay(args,manifest)

if __name__=='__main__': main()
