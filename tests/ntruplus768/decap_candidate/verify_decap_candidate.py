#!/usr/bin/env python3
"""Replay the candidate calculation, proofs, checkers and exact-splice API tests."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode = True
import check_decap_candidate as policy
import prepare_reference as reference
ROOT, TEST = policy.ROOT, policy.TEST
PROOF = ROOT / 'ntruplus/proof/768/ref/decap_candidate'
EXTRACTED = PROOF / 'extracted'
EXTRACTED_MAIN = 'NTRUPlus768DecapCandidate.ec'
GUARD_SOURCE = ROOT / 'ntruplus/jasmin/768/ref/decap_guard.jazz'
GUARD_PIN = '7e06fdb274a0b1f1cacecd4e4ffc330d959cd7cc11001a52ec74efd1bf1f64c4'
DECODER_PIN = '3bc951679734c56a327df50aecd505bb664905a8bfc2127f4b15a95da9d82b04'
GENERATED_EOF = '\nlemma __candidate_generated_eof : true. proof. trivial. qed.\n'


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def include_arguments():
    args, directories = [], []
    for raw in (PROOF / 'easycrypt.project').read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(('#', '[')):
            continue
        key, separator, value = line.partition('=')
        key, value = key.strip(), value.strip()
        policy.require(separator and key in ('rdirs', 'idirs', 'timeout'), 'unsupported project setting')
        if key == 'timeout':
            continue
        namespace, colon, directory = value.partition(':')
        if not colon:
            namespace, directory = '', value
        path = (PROOF / directory).resolve()
        policy.require(path.is_dir(), 'missing include directory: ' + str(path))
        directories.append(path)
        args += ['-R' if key == 'rdirs' else '-I', namespace + ':' + str(path) if colon else str(path)]
    return args, directories


def snapshot(directories):
    paths = policy.source_dependencies() | {GUARD_SOURCE, GUARD_SOURCE.parent / 'poly_frombytes.jazz',
        ROOT / 'scripts/verify-ntruplus768-decap-candidate.sh',
        TEST.parent / 'toolchain/check_model_compatibility.py',
        ROOT / 'NTRU+/NTRU+768/ntt.c', ROOT / 'NTRU+/NTRU+768/poly.c', reference.GUARD / 'prepare_reference.py',
        reference.GUARD / 'reference-manifest.json',
        TEST.parent / 'poly_frombytes_checked/check_poly_frombytes_checked.py',
        PROOF / 'Makefile', PROOF / 'easycrypt.project'}
    paths.update(p for p in TEST.rglob('*') if p.is_file() and p.suffix not in ('.pyc', '.eco'))
    paths.update(p for p in reference.REFERENCE.rglob('*') if p.is_file())
    for directory in directories:
        paths.update(directory.rglob('*.ec'))
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-only', action='store_true', help='never reports full proof PASS')
    parser.add_argument('--defer-safety', action='store_true', help='omit only safety analysis; report PASS_EXCEPT_SAFETY, never full PASS')
    parser.add_argument('--output', type=Path, help='new/empty evidence directory outside checkout')
    args = parser.parse_args()
    output = (args.output or Path(tempfile.mkdtemp(prefix='ntruplus-decap-candidate-'))).resolve()
    policy.require(not output.is_relative_to(ROOT), 'evidence must be outside checkout')
    output.mkdir(parents=True, exist_ok=True)
    policy.require(not any(output.iterdir()), 'output directory must be empty')
    summary = output / 'summary.json'
    report = {'status': 'RUNNING', 'started_at': timestamp(), 'output': str(output), 'commands': [], 'tools': {},
        'reference_commit': '3991b2ae08d6f0008d37e41b8aceaaab27b4ec89', 'platform': platform.platform(),
        'safety_replayed': False, 'safety_deferred': args.defer_safety,
        'scope': 'Candidate polynomial computation only; native mixed-C API regression for candidate-only and guard+candidate splices. Not complete Decaps, original-message recovery, C-AST equivalence or IND-CCA.',
        'buffer_contract': 'Three disjoint1536-byte u16-aligned regions. cp/fp initialized canonical coefficients0..3456; rp writable with no initial-value requirement. Output signed ternary coefficients. Guard+candidate native integration also inherits guard disjoint-region policy.',
        'ct_sct_policy': 'Candidate inputs/outputs secret, no declassification, public structural loop bounds. Reused guard has separately verified two key-canonicality-bit disclosures; combined native regression does not establish CT/SCT of remaining C API.',
        'native_scope': 'Exact official KAT RNG, immutable C dependencies and exact one/two-block splices. Trace counts exported calls and C continuation calls, not Jasmin internal loads. UBSan covers C only; Jasmin memory safety is checked separately.',
        'python': {'path': sys.executable, 'version': sys.version, 'sha256': digest(Path(sys.executable))},
        'environment': {'EC_TIMEOUT': os.environ.get('EC_TIMEOUT', '60'), 'max_provers': 1, 'prover': 'Z3'}}

    def save():
        temporary = summary.with_suffix('.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(summary)

    def run(label, argv, cwd=ROOT, expected_failure=False, overrides=None):
        log = output / (label + '.log')
        record = {'label': label, 'argv': [str(a) for a in argv], 'cwd': str(cwd), 'started_at': timestamp(),
                  'log': str(log), 'environment_overrides': overrides or {}}
        report['commands'].append(record); save()
        start = time.monotonic()
        with log.open('w') as stream:
            process = subprocess.run(record['argv'], cwd=cwd, env={**os.environ, **(overrides or {})}, stdout=stream, stderr=subprocess.STDOUT)
        okay = process.returncode != 0 if expected_failure else process.returncode == 0
        record.update(exit_code=process.returncode, seconds=round(time.monotonic()-start, 3),
                      completed_at=timestamp(), log_sha256=digest(log), expected_failure=expected_failure,
                      result='EXPECTED_REJECTION' if okay and expected_failure else 'PASS' if okay else 'FAIL')
        save(); print(record['result'], label, record['seconds'], flush=True)
        if not okay:
            print('\n'.join(log.read_text(errors='replace').replace('\r','\n').splitlines()[-25:]))
            raise RuntimeError('command failed: ' + label)
        return log

    def tool(variable, name, version):
        argv = shlex.split(os.environ.get(variable, name))
        path = shutil.which(argv[0]); policy.require(path, 'missing tool: ' + argv[0])
        argv[0] = str(Path(path).resolve())
        log = run('tool-' + name, argv + version)
        report['tools'][name] = {'argv_prefix': argv, 'binary_sha256': digest(Path(argv[0])), 'version': log.read_text(errors='replace')}
        return argv

    directories = []
    save()
    try:
        include, directories = include_arguments()
        report['source_hashes_before'] = snapshot(directories)
        policy.check()
        policy.require(digest(GUARD_SOURCE) == GUARD_PIN and digest(GUARD_SOURCE.parent / 'poly_frombytes.jazz') == DECODER_PIN,
                       'reused guard/decoder source pin drift')
        run('source-model-compatibility', [sys.executable, TEST.parent / 'toolchain/check_model_compatibility.py', '--source-only'])
        run('source-policy-check', [sys.executable, TEST / 'check_decap_candidate.py'])
        run('mutation-gate-selfcheck', [sys.executable, TEST / 'test_gates.py'])
        audit = run('official-arithmetic-compatibility', [sys.executable, TEST / 'audit_compatibility.py', '--root', ROOT])
        report['official_arithmetic_compatibility'] = json.loads(audit.read_text())
        jasmin = tool('JASMINC', 'jasminc', ['-version'])
        extractor = tool('JASMIN2EC', 'jasmin2ec', ['--version'])
        safety = tool('JASMIN_CHECKSAFETY', 'jasmin-checksafety', ['--version'])
        ct = tool('JASMINCT' if 'JASMINCT' in os.environ else 'JASMIN_CT', 'jasmin-ct', ['--version'])
        cc = tool('CC', 'cc', ['--version'])
        easycrypt = tool('EASYCRYPT', 'easycrypt', ['config']) if not args.native_only else []
        if not args.native_only:
            tool('WHY3', 'why3', ['--version'])
        run('compiler-target', cc + ['-dumpmachine'])
        fresh = output / 'fresh-extraction'; fresh.mkdir()
        run('fresh-extraction', extractor + ['--array-model=old', '--arch=x86-64', '--cc=linux', '--output-array=' + str(fresh),
            '-o', str(fresh / EXTRACTED_MAIN), '-f', policy.SLICE, str(policy.SOURCE)])
        report['fresh_extraction'] = {'result': 'PASS', 'files': policy.check_extraction(EXTRACTED, fresh), 'comparison': 'whole inventory and raw bytes'}
        guard_fresh = output / 'guard-fresh-extraction'; guard_fresh.mkdir()
        run('guard-fresh-extraction', extractor + ['--array-model=old', '--arch=x86-64', '--cc=linux', '--output-array=' + str(guard_fresh),
            '-o', str(guard_fresh / 'NTRUPlus768DecapGuard.ec'), '-f', 'jade_ntruplus_ntruplus768_amd64_ref_decap_guard', str(GUARD_SOURCE)])
        guard_stored = ROOT / 'ntruplus/proof/768/ref/decap_guard/extracted'
        guard_expected = {'Array1152.ec', 'Array2304.ec', 'Array32.ec', 'Array768.ec', 'WArray1152.ec', 'WArray1536.ec',
                          'WArray2304.ec', 'WArray32.ec', 'NTRUPlus768DecapGuard.ec'}
        guard_before = {p.name:p.read_bytes() for p in guard_stored.iterdir() if p.is_file()}
        guard_after = {p.name:p.read_bytes() for p in guard_fresh.iterdir() if p.is_file()}
        policy.require(set(guard_before) == set(guard_after) == guard_expected and guard_before == guard_after,
                       'reused guard raw extraction/inventory drift')
        report['reused_guard_fresh_extraction'] = {'result':'PASS', 'files':{n:policy.sha(v) for n,v in guard_after.items()}}
        for name, source, export in [('candidate', policy.SOURCE, policy.SLICE), ('guard', GUARD_SOURCE, 'jade_ntruplus_ntruplus768_amd64_ref_decap_guard')]:
            run('compile-' + name, jasmin + ['-arch', 'x86-64', '-call-conv', 'linux', '-system', 'linux', '-slice', export,
                                          '-o', str(output / (name + '.s')), str(source)])
        if not args.native_only:
            import eof_sentinels as eof
            new = {p.name for p in PROOF.glob('*.ec')}
            policy.require(new == set(eof.PROOF_PINS) == set(eof.SENTINELS), 'new proof inventory drift')
            targets = [(p, GENERATED_EOF, None) for p in sorted(EXTRACTED.glob('*.ec'))]
            targets += [(ROOT / p, v['sentinel'], v['sha256']) for p,v in eof.REUSED.items()]
            targets += [(PROOF / p, eof.SENTINELS[p], h) for p,h in eof.PROOF_PINS.items()]
            timeout = int(report['environment']['EC_TIMEOUT']); policy.require(timeout > 0, 'positive EC_TIMEOUT required')
            server = []
            if os.environ.get('WHY3_SERVER_SOCKET'):
                socket = Path(os.environ['WHY3_SERVER_SOCKET']); policy.require(socket.is_socket(), 'invalid Why3 socket')
                server = ['-server', str(socket)]
            def proof_command(path):
                return easycrypt + ['compile', '-no-eco', '-pragmas', 'Proofs:check', '-p', 'Z3', '-timeout', str(timeout),
                                    '-max-provers', '1', *server, *include, str(path)]
            report['proof_mains'] = []
            for index, (path, sentinel, pin) in enumerate(targets):
                original = path.read_bytes(); relative = str(path.relative_to(ROOT))
                policy.require(policy.sha(original) == report['source_hashes_before'][relative], 'proof source changed before replay')
                if pin:
                    policy.require(policy.sha(original) == pin, 'reviewed proof pin drift: ' + relative)
                    policy.check_proof_text(original.decode())
                directory = output / 'proof-inputs' / str(index); directory.mkdir(parents=True)
                copied = directory / path.name; copied.write_bytes(original + sentinel.encode()); copied_hash = digest(copied)
                log = run('proof-' + path.stem, proof_command(copied), cwd=PROOF)
                policy.require(digest(copied) == copied_hash, 'proof copy mutated during replay')
                report['proof_mains'].append({'source':relative, 'source_sha256':policy.sha(original), 'checked_copy':str(copied),
                    'checked_copy_sha256':copied_hash, 'sentinel_sha256':policy.sha(sentinel.encode()), 'result':'PASS', 'log':str(log)})
            name = 'NTRUPlus768DecapCandidateProof.ec'; original = (PROOF / name).read_text(); cut = original.rfind('qed.')
            policy.require(cut >= 0 and not original[cut+4:].strip(), 'unexpected final proof structure')
            negative = output / 'open-proof' / name; negative.parent.mkdir()
            negative.write_text(original[:cut] + eof.SENTINELS[name])
            log = run('eof-open-proof-rejection', proof_command(negative), cwd=PROOF, expected_failure=True)
            policy.require('inside a proof script' in log.read_text(errors='replace'), 'EOF rejection reason changed')
        safety_command = safety + ['--arch=x86-64', '--call-conv=linux', '--slice=' + policy.SLICE, str(policy.SOURCE)]
        report['safety'] = {'status': 'DEFERRED' if args.defer_safety else 'RUNNING', 'argv': safety_command,
                            'source_hashes': {str(p.relative_to(ROOT)): digest(p) for p in sorted(policy.source_dependencies())},
                            'checker_sha256': report['tools']['jasmin-checksafety']['binary_sha256'],
                            'reason': 'Explicit --defer-safety; separate fresh safety evidence is still required.' if args.defer_safety else ''}
        if not args.defer_safety:
            safety_log = run('candidate-safety', safety_command)
            policy.require('No Safety Violation' in safety_log.read_text(), 'missing positive safety diagnostic')
            report['safety'].update(status='PASS', log=str(safety_log), log_sha256=digest(safety_log))
            report['safety_replayed'] = True
        run('candidate-ct', ct + ['--after=inline', '--slice=' + policy.SLICE, str(policy.SOURCE)])
        run('candidate-sct', ct + ['--sct', '--after=inline', '--slice=' + policy.SLICE, str(policy.SOURCE)])
        generated = output / 'generated-c'
        run('prepare-reference-splice', [sys.executable, TEST / 'prepare_reference.py', '--output', generated])
        report['reference_splice'] = json.loads((generated / 'splice.json').read_text())
        native_sources = [TEST / 'decap_candidate_test.c', TEST / 'trace.c'] + [generated / (name + '_kem.c') for name in ('official', 'mixed', 'both')]
        native_sources += [reference.REFERENCE / name for name in ('poly.c', 'ntt.c', 'symmetric.c', 'fips202/fips202.c', 'kat/rng.c', 'kat/aes.c')]
        native_sources += [output / 'candidate.s', output / 'guard.s']
        report['native_compiled_sources'] = {str(p): digest(p) for p in native_sources}
        report['differential'] = {}
        for variant in ('normal', 'ubsan'):
            directory = output / ('native-' + variant); directory.mkdir()
            flags = ['-std=c11', '-O2', '-g', '-Wall', '-Wextra', '-Wpedantic', '-ffunction-sections', '-fdata-sections',
                     '-I' + str(TEST), '-I' + str(reference.REFERENCE)]
            sanitizer = ['-O1', '-fsanitize=undefined', '-fno-sanitize-recover=undefined', '-fno-omit-frame-pointer'] if variant == 'ubsan' else []
            objects = []
            for index, path in enumerate(native_sources):
                obj = directory / (str(index) + '.o')
                extra = ['-Werror'] if path.parent == TEST else []
                if path.name == 'rng.c': extra += ['-Drandombytes=kat_randombytes', '-include', 'stdlib.h']
                run('native-' + variant + '-compile-' + str(index), cc + flags + sanitizer + extra + ['-c', str(path), '-o', str(obj)])
                objects.append(str(obj))
            binary = directory / 'decap-candidate-test'
            run('native-' + variant + '-link', cc + objects + sanitizer + ['-Wl,--gc-sections', '-Wl,-z,noexecstack', '-o', str(binary)])
            log = run('native-' + variant + '-run', [binary, reference.REFERENCE / 'PQCkemKAT_2336.rsp'],
                      overrides={'UBSAN_OPTIONS':'halt_on_error=1:print_stacktrace=1'} if variant == 'ubsan' else {})
            counts = json.loads(log.read_text())
            expected = {'status':'PASS', 'candidate_cases':69428, 'kat_api_runs':300, 'malformed_api_triples':4622,
                        'canonical_api_triples':356, 'fresh_api_triples':32}
            policy.require(all(counts.get(k) == v for k,v in expected.items()), 'incomplete native coverage')
            counts['binary_sha256'] = digest(binary); report['differential'][variant] = counts
        report['native_compiled_sources_after'] = {str(p):digest(p) for p in native_sources}
        policy.require(report['native_compiled_sources'] == report['native_compiled_sources_after'], 'native inputs changed during replay')
        status = 'NATIVE_PASS' if args.native_only else 'PASS'
        if args.defer_safety: status += '_EXCEPT_SAFETY'
        report.update(status=status, proofs_replayed=not args.native_only)
    except Exception as error:
        report.update(status='FAIL', error_type=type(error).__name__, error=str(error))
    finally:
        if directories and 'source_hashes_before' in report:
            try:
                report['source_hashes_after'] = snapshot(directories)
                report['inputs_unchanged'] = report['source_hashes_before'] == report['source_hashes_after']
                if not report['inputs_unchanged']: report.update(status='FAIL', error='source inputs changed during replay')
            except (OSError, ValueError) as error:
                report.update(status='FAIL', inputs_unchanged=False, error='source snapshot failed: ' + str(error))
        report['completed_at'] = timestamp(); save()
    print('RESULT', report['status'], str(summary), flush=True)
    return 0 if report['status'] in ('PASS', 'NATIVE_PASS', 'PASS_EXCEPT_SAFETY', 'NATIVE_PASS_EXCEPT_SAFETY') else 1


if __name__ == '__main__':
    sys.exit(main())
