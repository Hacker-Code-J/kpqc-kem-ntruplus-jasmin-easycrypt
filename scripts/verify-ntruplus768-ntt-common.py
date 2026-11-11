#!/usr/bin/env python3
"""Check the shared composition theorem and its actual NTRU+ kernel instance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--dependencies', action='store_true',
                        help='also replay every local proof in the instance dependency closure')
    args = parser.parse_args()
    root = args.root.resolve()
    source_dir = root / 'ntruplus/proof/768/ref/ntt_common'
    semantics = source_dir.parent / 'ring_semantics'
    out = args.output or Path(tempfile.mkdtemp(prefix='ntruplus-ntt-common-'))
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run(['python3', str(root / 'tests/ntruplus768/toolchain/check_model_compatibility.py'),
                    '--source-only'], check=True)
    pin = json.loads((source_dir / 'SOURCE.json').read_text())
    shared = source_dir / 'NTTComposition.ec'
    if digest(shared) != pin['shared_sha256']:
        raise ValueError('Shared NTT composition source differs from its recorded version')
    printed = subprocess.run(['make', '--no-print-directory', '-n', 'ntt-basemul-invntt',
                              'EASYCRYPT=easycrypt'], cwd=semantics, capture_output=True,
                             text=True, check=True).stdout
    command = shlex.split(next(line for line in printed.splitlines()
                              if line.startswith('easycrypt compile')))
    directories = [source_dir] + [(semantics / command[i + 1]).resolve()
                                  for i, part in enumerate(command) if part == '-I']
    libraries = {}
    for directory in directories:
        for path in directory.glob('*.ec'):
            if path.stem in libraries and digest(path) != digest(libraries[path.stem]):
                raise ValueError(f'Conflicting EasyCrypt theory: {path.stem}')
            libraries.setdefault(path.stem, path)
    visited, ordered = set(), []

    def visit(path):
        if path in visited:
            return
        visited.add(path)
        text = re.sub(r'\(\*.*?\*\)', ' ', path.read_text(), flags=re.S)
        for match in re.finditer(r'\brequire\s+(?:(?:import|export)\s+)?([^.;]+)\.', text):
            for name in match.group(1).split():
                if name in libraries:
                    visit(libraries[name])
        ordered.append(path)

    instance = source_dir / 'NTRUPlus768NTTComposition.ec'
    visit(instance)
    inputs = {str(path): digest(path) for path in ordered}
    shim = root / 'ntruplus/proof/compat/jasmin/JModel.ec'
    inputs[str(shim)] = digest(shim)
    (out / 'inputs.json').write_text(json.dumps(inputs, indent=2))
    own = [shared, instance]
    for path in own:
        text = re.sub(r'\(\*.*?\*\)', ' ', path.read_text(), flags=re.S)
        if re.search(r'\b(admit|admitted|abort|assume|axiom|sorry|pragma)\b', text):
            raise ValueError(f'Unpermitted proof declaration in {path.name}')
        if re.search(r'(?m)^\s*print\s+(goal|all)\b', text):
            raise ValueError(f'Debug command in {path.name}')
    local_root = root / 'ntruplus/proof/768/ref'
    targets = [path for path in ordered if path.is_relative_to(local_root)
               and 'extracted' not in path.parts] if args.dependencies else own
    results = []
    for path, negative in [(p, False) for p in targets] + [(p, True) for p in own]:
        run = out / (path.stem + ('-negative' if negative else '-checked'))
        run.mkdir()
        copy = run / path.name
        pending = '\nlemma __unfinished_control : true.\nproof.\n' if negative else ''
        copy.write_text(path.read_text() + pending +
                        '\nlemma __ntt_eof_complete : true.\nproof. trivial. qed.\n')
        cmd = [os.environ.get('EASYCRYPT', 'easycrypt'), 'compile', '-no-eco',
               '-pragmas', 'Proofs:check', '-timeout', os.environ.get('EC_TIMEOUT', '30'),
               '-max-provers', '1', '-I', str(path.parent)]
        for directory in directories:
            cmd += ['-I', str(directory)]
        cmd += ['-I', 'Jasmin:' + str(shim.parent), str(copy)]
        start = time.monotonic()
        with (run / 'compile.log').open('w') as log:
            result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT)
        output = (run / 'compile.log').read_text(errors='replace')
        ok = result.returncode != 0 and 'cannot process [axiom] inside a proof script' in output \
            if negative else result.returncode == 0
        for name, value in inputs.items():
            if digest(Path(name)) != value:
                raise ValueError(f'Input changed while checking: {name}')
        results.append({'target': str(path.relative_to(root)), 'sha256': digest(path),
                        'negative_eof': negative, 'exit_code': result.returncode, 'success': ok,
                        'seconds': round(time.monotonic() - start, 3), 'command': cmd})
        report = {'result': 'PASS' if all(r['success'] for r in results) else 'FAIL',
                  'dependencies_replayed': args.dependencies, 'results': results}
        (out / 'summary.json').write_text(json.dumps(report, indent=2))
        print('PASS' if ok else 'FAIL', path.name, 'negative' if negative else 'proof', flush=True)
        if not ok:
            print(output[-3000:])
            return 1
    print(f'NTT common composition checks passed; evidence: {out}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
