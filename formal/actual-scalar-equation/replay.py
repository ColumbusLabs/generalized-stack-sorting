#!/usr/bin/env python3
"""Fresh source-only Lean 4.34.1 replay. Retain every attempt; no wall-time cutoff."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
import verify_sources as package

R = Path(__file__).resolve().parent
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
BASELINES = {
    'CauchyRing': 'f503c3f5534d3c596b0b41b4d5d309aa9aa2dd2245d33078bd4679a58aaf5a34',
    'SeriesPolynomialSemantics': '22aaae5b5224620c0e4b758d5d049ece6173988f84e000465a17368fb9e44807',
    'ScalarSeriesCertificate': '0988f2431f6f1ead4157970a6873c8f4129267db4f239419069f0afd01f5a58e',
    'ScalarBranchUnique': 'f83e8bc596cf0b730d3f99155c1abc54c4024ae112008f53a506d8e30eb6e308',
}
THEOREMS = [
    'StackSorting.Generalized.Decorated.SignedCompletion.literal_G_counts',
    'StackSorting.Generalized.Decorated.SignedCompletion.actual_counts_literalQ',
]

def memory_gate():
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))
    if available < 6291456:
        raise RuntimeError('Fresh memory qualification requires at least 6 GiB MemAvailable; all existing attempt evidence is retained.')
    return available

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    lean = str(Path(args.lean).resolve())
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    manifest, policy = package.verify()
    assert manifest['compile_policy']['nonfatal_warning_exceptions'] == BASELINES
    build = out / 'build'
    package.materialize_sources(build, manifest)
    env = dict(os.environ, LEAN_PATH=str(build), NO_COLOR='1')
    for variable in ['LEAN_SYSROOT', 'LEAN_OPTS']:
        env.pop(variable, None)
    version = subprocess.check_output([lean, '--version'], text=True, env=env)
    assert re.search(r'\bversion 4\.34\.1\b', version), version
    (out / 'TOOLCHAIN.json').write_text(json.dumps({'version': version, 'executable_sha256': H(lean),
        'isolated_lean_path': str(build), 'project_object_reuse': False}, indent=2) + '\n')
    warnings = {item['module']: item['exact_warning_headlines'] for item in policy['exceptions']}
    rows = {item['module']: item for item in manifest['modules']}
    records, objects = [], {}
    for module in manifest['compile_order']:
        relative = module.replace('.', '/')
        source = build / (relative + '.lean')
        assert H(source) == rows[module]['sha256']
        strict = module not in BASELINES
        if not strict:
            assert H(source) == BASELINES[module]
        available = memory_gate()
        target = build / (relative + '.olean')
        assert not target.exists()
        command = [lean, '-j1', '-DwarningAsError=' + str(strict).lower(), '-o', str(target), relative + '.lean']
        started = time.monotonic()
        result = subprocess.run(command, cwd=build, env=env, capture_output=True, text=True)
        log = out / 'logs' / relative
        log.parent.mkdir(parents=True, exist_ok=True)
        Path(str(log) + '.stdout.log').write_text(result.stdout)
        Path(str(log) + '.stderr.log').write_text(result.stderr)
        combined = result.stdout + result.stderr
        headlines = [line for line in combined.splitlines() if ': warning:' in line]
        expected = warnings.get(module, [])
        passed = result.returncode == 0 and target.is_file() and headlines == expected
        imported_objects = {m: objects[m] for m in rows[module]['imports'] if m in rows}
        row = {'module': module, 'source_sha256': H(source), 'source_closure_sha256': rows[module]['closure_sha256'],
            'exit_code': result.returncode, 'passed': passed, 'warning_as_error': strict,
            'warning_headlines': headlines, 'exact_expected_warning_headlines': expected,
            'prelaunch_available_kib': available, 'seconds': time.monotonic() - started,
            'command': command, 'imported_object_sha256': imported_objects,
            'object_sha256': H(target) if target.is_file() else None}
        records.append(row)
        (out / 'CASES.json').write_text(json.dumps(records, indent=2) + '\n')
        print(json.dumps({k: row[k] for k in ['module', 'source_sha256', 'exit_code', 'passed', 'warning_as_error', 'seconds']}), flush=True)
        assert passed, row
        objects[module] = row['object_sha256']
    endpoint_log = (out / 'logs/GeneralizedActualScalarEquation.stdout.log').read_text()
    axiom_records = {}
    for name in THEOREMS:
        pattern = re.escape("'" + name + "' depends on axioms:") + r'\s*\[([^]]*)\]'
        matches = re.findall(pattern, endpoint_log)
        assert len(matches) == 1, (name, endpoint_log)
        axioms = [item.strip() for item in matches[0].split(',')]
        assert sorted(axioms) == sorted(['propext', 'Classical.choice', 'Quot.sound']), (name, axioms)
        axiom_records[name] = axioms
    (out / 'SUMMARY.json').write_text(json.dumps({'status': 'SOURCE_ONLY_REPLAY_PASS',
        'original_source_manifest_sha256': package.EXPECTED_ORIGINAL,
        'source_modules': len(records), 'warning_exception_count': len(BASELINES),
        'project_object_reuse': False, 'theorem_axioms': axiom_records,
        'scope': 'Exact 1,613-module source closure; all-length literal (3,3) actual-count scalar equation.',
        'guard_result_required': '../guard/result.json'}, indent=2) + '\n')

if __name__ == '__main__':
    main()
