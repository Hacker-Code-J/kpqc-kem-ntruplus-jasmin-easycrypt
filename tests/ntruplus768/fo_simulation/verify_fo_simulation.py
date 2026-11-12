#!/usr/bin/env python3
"""Classical-ROM actual FO-to-public-simulator adaptive win-distance replay; source-only checks never receive full PASS."""
import argparse
import ast
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
import threading

sys.dont_write_bytecode = True
import check_fo_simulation as policy
ROOT, TEST, BASE = policy.ROOT, policy.TEST, policy.BASE


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return policy.sha(path.read_bytes())


def check_negative_diagnostic(diagnostic, path):
    policy.require('external theory' not in diagnostic.lower(), 'negative failed while importing another theory')
    match = re.search(r'\[critical\]\s*\[' + re.escape(str(path)) + r':[^\r\n]+', diagnostic)
    policy.require(match and 'cannot process [axiom] inside a proof script' in match.group(),
                   'negative must fail at its own unfinished proof, not another location')
    return match.group()


def check_sentinel(name, sentinel, target, module_binders, source_text=None):
    policy.check_proof_text(sentinel)
    code = policy.compact(sentinel)
    policy.require(code.count('lemma__') == 1 and code.endswith('qed.'),
                   'EOF sentinel must be one completed named lemma: ' + name)
    policy.require(re.search(r'\bproof\.\s*exact\s*\(?\s*' + re.escape(target) + r'\b', policy.without_comments(sentinel)),
                   'EOF sentinel does not reference its reviewed semantic theorem: ' + name)
    policy.require(not re.search(r':(?:true|false)\.', code), 'constant EOF proposition: ' + name)
    # Any module binders in these new symbolic sentinels must be syntactic
    # module parameters, rather than silently inferred ordinary variables.
    actual = set(re.findall(r'\((\w+)\s*<:', policy.without_comments(sentinel)))
    policy.require(actual == set(module_binders), 'EOF explicit module binder inventory: ' + name)
    if name in policy.MAINS or source_text is not None:
        source = policy.without_comments(source_text if source_text is not None else (policy.BASE / name).read_text())
        declarations = re.findall(r'\blemma\s+' + re.escape(target) + r'\b(.*?)\bproof\.', source, re.S)
        sentinel_declaration = re.search(r'\blemma\s+\w+\b(.*?)\bproof\.',
                                         policy.without_comments(sentinel), re.S)
        policy.require(len(declarations) == 1 and sentinel_declaration is not None,
                       'EOF semantic declaration is not uniquely resolved: ' + name)
        policy.require(policy.compact(declarations[0]) == policy.compact(sentinel_declaration.group(1)),
                       'EOF statement differs from the frozen semantic theorem declaration: ' + name)




def last_proof_closer(original):
    """Locate the last proof closer outside nested comments."""
    depth, offset, closers = 0, 0, []
    for token in re.split(r'(\(\*|\*\))', original):
        if token == '(*':
            depth += 1
        elif token == '*)':
            policy.require(depth > 0, 'unmatched EasyCrypt comment terminator')
            depth -= 1
        elif depth == 0:
            closers.extend(offset + match.start() for match in re.finditer(r'\bqed\.', token))
        offset += len(token)
    policy.require(depth == 0, 'unclosed EasyCrypt comment')
    policy.require(closers, 'negative source has no completed proof')
    return closers[-1]


def completed_proof_text(original, sentinel):
    # Keep a scoped theorem inside its abstract theory; retain trailing declarations.
    end = last_proof_closer(original) + 4
    return original[:end] + sentinel + original[end:]


def unfinished_proof_text(original, sentinel):
    cut = last_proof_closer(original)
    return original[:cut] + sentinel + original[cut + 4:]


def run_phase(worker, names, jobs):
    """Join every worker and return results in input order; any failure propagates."""
    policy.require(jobs in (1, 2), 'EC_JOBS must be 1 or 2')
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [executor.submit(worker, index, name) for index, name in enumerate(names)]
        return [future.result() for future in futures]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only', action='store_true', help='source/mutation/syntax checks; never full PASS')
    parser.add_argument('--output', type=Path, help='new/empty evidence directory outside checkout')
    parser.add_argument('--prior-evidence-root', type=Path,
                        default=ROOT.parent / 'research-evidence',
                        help='thesis root holding the hash-linked prior evidence')
    args = parser.parse_args()
    output = (args.output or Path(tempfile.mkdtemp(prefix='ntruplus-fo-simulation-'))).resolve()
    policy.require(not output.is_relative_to(ROOT), 'evidence must be outside checkout')
    output.mkdir(parents=True, exist_ok=True)
    policy.require(not any(output.iterdir()), 'output must be empty')
    report = {'status': 'RUNNING', 'started_at': timestamp(), 'output': str(output),
              'platform': platform.platform(), 'commands': [], 'tools': {}, 'per_command_log_limit_bytes': 33554432,
              'scope': 'Actual uncapped FOFreshReencryptGame versus secret-key-free SimPublicFreshGame adaptive win distance in the classical ROM, under explicit robust-losslessness and query-count contracts; not a full IND-CCA reduction.',
              'proof_scope': 'Only the listed new mains are freshly checked. Imported theories are conservatively hash-bound prior evidence, not fresh main replays.',
              'call_scope': 'Public typed/raw H history is distinct from the physical H table. Secret-key-free lookup uses logged full replies and actual encryption calls; cached replies and future public queries remain consistent.',
              'not_claimed': ['full IND-CCA hardness reduction', 'absence from public history implies physical H freshness', 'raw zero-output callers receive the full internal H record', 'an averaged error bound holds at every fixed key and G', 'cached H hits may resample', 'returned bad mass counts events before divergence without a termination argument', 'actual ROM KeyGen losslessness', 'fixed SHAKE versus ROM equivalence', 'native replay', 'new Jasmin extraction', 'Safety/CT/SCT replay'],
              'prior_evidence': [],
              'import_axiom_scope': 'Standard library and prior imported theories retain their existing scoped axioms. No new local axiom/admit is permitted; new public-history, actual-call, fresh-hash and explicitly contextual simulation laws are checked mains.',
              'python': {'path': sys.executable, 'version': sys.version, 'sha256': digest(Path(sys.executable))},
              'environment': {'EC_TIMEOUT': int(os.environ.get('EC_TIMEOUT', '60')),
                              'EC_JOBS': int(os.environ.get('EC_JOBS', '2')),
                              'OCAMLRUNPARAM': 'o=20', 'max_provers': 1, 'prover': 'Z3',
                              'Proofs': 'check', 'eco': False},
              'declared_proof_mains': len(policy.MAINS),
              'declared_negative_proofs': len(policy.MAINS),
              'proof_mains': [], 'negative_proofs': []}
    summary = output / 'summary.json'
    report_lock = threading.RLock()

    def save():
        with report_lock:
            temporary = summary.with_suffix('.tmp')
            temporary.write_text(json.dumps(report, indent=2) + '\n')
            temporary.replace(summary)

    def run(label, argv, expected_failure=False, cwd=ROOT):
        log = output / (label + '.log')
        record = {'label': label, 'argv': [str(x) for x in argv], 'cwd': str(cwd),
                  'started_at': timestamp(), 'log': str(log), 'expected_failure': expected_failure}
        with report_lock:
            report['commands'].append(record)
            save()
        start = time.monotonic()
        overflow = False
        with log.open('wb') as stream:
            process = subprocess.Popen(record['argv'], cwd=cwd,
                                       env={**os.environ, 'OCAMLRUNPARAM': 'o=20', 'PYTHONDONTWRITEBYTECODE': '1'},
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            emitted = 0
            while chunk := process.stdout.read1(65536):
                emitted += len(chunk)
                if emitted > report['per_command_log_limit_bytes']:
                    overflow = True
                    process.kill()
                    stream.write(b'\nHARNESS: command exceeded the bounded log budget.\n')
                    break
                stream.write(chunk)
                stream.flush()
            process.stdout.close()
            process.wait()
        okay = not overflow and (process.returncode != 0 if expected_failure else process.returncode == 0)
        with report_lock:
            record.update(exit_code=process.returncode, log_limit_exceeded=overflow, seconds=round(time.monotonic() - start, 3),
                          completed_at=timestamp(), log_sha256=digest(log),
                          result='EXPECTED_REJECTION' if okay and expected_failure else 'PASS' if okay else 'FAIL')
            save()
        print(record['result'], label, record['seconds'], flush=True)
        if not okay:
            print('\n'.join(log.read_text(errors='replace').replace('\r', '\n').splitlines()[-20:]))
            raise RuntimeError('command failed: ' + label)
        return log

    external = {Path(sys.executable).resolve(), Path(shutil.which('bash')).resolve()}

    def bind_prior_evidence():
        pins = json.loads((TEST / 'prior-evidence-pins.json').read_text())
        imported = {str(p.relative_to(ROOT)): digest(p) for p in policy.source_paths()
                    if p.suffix == '.ec' and not any(g in p.parts for g in policy.GROUPS)}
        covered = set()
        for relative, expected in pins.items():
            path = (args.prior_evidence_root.resolve() / relative).resolve()
            policy.require(path.is_file() and not path.is_symlink(), 'prior evidence missing: ' + relative)
            policy.require(digest(path) == expected, 'prior evidence pin drift: ' + relative)
            prior = json.loads(path.read_text())
            policy.require(prior['status'] == 'PASS', 'prior evidence is not a PASS: ' + relative)
            policy.require(prior.get('inputs_unchanged') is True and
                           prior['source_hashes_before'] == prior['source_hashes_after'],
                           'prior source audit is not stable: ' + relative)
            prior_external_audit = 'not present in legacy record; source provenance only'
            if 'external_hashes_before' in prior:
                policy.require(prior.get('external_inputs_unchanged') is True and
                               prior['external_hashes_before'] == prior['external_hashes_after'],
                               'prior tool/config/theory audit is not stable: ' + relative)
                prior_external_audit = 'stable before/after audit in hash-linked record'
            matched = []
            for source, value in imported.items():
                if source in prior['source_hashes_after']:
                    policy.require(value == prior['source_hashes_after'][source],
                                   'import differs from prior verified source: ' + source)
                    matched.append(source)
                    covered.add(source)
            external.add(path)
            report['prior_evidence'].append({'path': str(path), 'sha256': expected,
                                             'status': prior['status'],
                                             'matched_imported_ec': len(matched),
                                             'external_audit': prior_external_audit,
                                             'scope': 'hash-linked prior result; no fresh replay'})
        policy.require(covered == set(imported), 'imported theory lacks prior source provenance')
        report['prior_imported_source_hashes'] = imported

    def tool(name, default, version):
        value = os.environ.get(name.upper(), default)
        path = Path(value)
        policy.require(path.is_absolute() and path.is_file(), name.upper() + ' must name an absolute executable path')
        path = path.resolve()
        external.add(path)
        log = run('tool-' + name, [path, *version], cwd=BASE)
        report['tools'][name] = {'path': str(path), 'sha256': digest(path), 'version': log.read_text()}
        return path

    try:
        jobs = report['environment']['EC_JOBS']
        policy.require(jobs in (1, 2), 'EC_JOBS must be 1 or 2')
        report['source_hashes_before'] = policy.snapshot()
        pins = policy.check()
        report['pinned_sources'] = len(pins)
        for path in sorted(TEST.glob('*.py')):
            ast.parse(path.read_text(), filename=str(path))
        ast.parse(policy.ENTRY.read_text(), filename=str(policy.ENTRY))
        report['python_ast'] = 'PASS'
        run('shell-syntax', ['bash', '-n', policy.SCRIPT])
        run('source-policy', [sys.executable, TEST / 'check_fo_simulation.py'])
        log = run('mutation-gates', [sys.executable, TEST / 'test_gates.py'])
        report['mutation_controls'] = json.loads(log.read_text())
        import eof_sentinels as eof
        report['negative_preflight'] = []
        policy.require(set(eof.NEGATIVE_PROOFS) == set(policy.MAINS), 'negative preflight inventory drift')
        for name in eof.NEGATIVE_PROOFS:
            path = BASE / name
            original = path.read_bytes().decode('utf-8')
            check_sentinel(name, eof.SENTINELS[name], eof.SEMANTIC_TARGETS[name], eof.MODULE_BINDERS[name])
            prepared = unfinished_proof_text(original, eof.SENTINELS[name])
            report['negative_preflight'].append({'source': str(path.relative_to(ROOT)),
                                                 'prepared_sha256': policy.sha(prepared.encode())})
        policy.require(len(report['negative_preflight']) == report['declared_negative_proofs'],
                       'negative preflight count')
        log = run('finite-domain-diagnostics', [sys.executable, TEST / 'test_reference.py'])
        report['finite_domain_diagnostics'] = json.loads(log.read_text())
        bind_prior_evidence()
        if args.check_only:
            report['external_hashes_before'] = {str(p): digest(p) for p in sorted(external)}
            report['status'] = 'SOURCE_CHECK_ONLY'
        else:
            import eof_sentinels as eof
            policy.require(set(eof.SENTINELS) == set(policy.MAINS), 'semantic EOF inventory drift')
            policy.require(set(eof.SEMANTIC_TARGETS) == set(policy.MAINS), 'semantic EOF target inventory drift')
            policy.require(set(eof.MODULE_BINDERS) == set(policy.MAINS), 'semantic EOF binder inventory drift')
            policy.require(set(eof.NEGATIVE_PROOFS) == set(policy.MAINS), 'one unfinished-proof control per main required')
            prefix = str(Path.home() / '.opam/cryptotools-2026.09')
            easycrypt = tool('easycrypt', prefix + '/bin/easycrypt', ['config'])
            why3 = tool('why3', prefix + '/bin/why3', ['--version'])
            config = report['tools']['easycrypt']['version']
            why_match = re.search(r'why3 configuration file\s*\n\s*(\S+)', config)
            policy.require(why_match, 'effective Why3 configuration absent')
            why_config = Path(why_match.group(1))
            external.add(why_config)
            blocks = re.split(r'(?m)^\[', why_config.read_text())
            z3_paths = {m.group(1) for b in blocks if re.search(r'(?m)^name\s*=\s*"Z3"', b)
                        for m in re.finditer(r'(?m)^(?:path|command)\s*=\s*"([^" ]+)', b)}
            policy.require(len(z3_paths) == 1, 'effective Z3 executable ambiguous')
            z3 = Path(z3_paths.pop()).resolve()
            external.add(z3)
            log = run('tool-z3', [z3, '--version'])
            report['tools']['z3'] = {'path': str(z3), 'sha256': digest(z3), 'version': log.read_text()}
            for line in config.splitlines():
                name = line.strip()
                if name.startswith('/') and name.endswith('.conf') and Path(name).is_file():
                    external.add(Path(name))
                if '@/' in name:
                    directory = Path(name.split('@', 1)[1])
                    if directory.is_dir() and not directory.is_relative_to(ROOT):
                        external.update(directory.rglob('*.ec'))
            for directory in (why3.parent.parent / 'share/why3', easycrypt.parent.parent / 'lib/easycrypt/config'):
                if directory.is_dir():
                    external.update(p for p in directory.rglob('*') if p.is_file())
            for name in ('why3server', 'why3cpulimit'):
                path = why3.parent.parent / 'lib/why3' / name
                policy.require(path.is_file(), 'missing Why3 helper: ' + name)
                external.add(path)
            report['external_hashes_before'] = {str(p): digest(p) for p in sorted(external)}
            for name, value in report['tools'].items():
                policy.require(report['external_hashes_before'][value['path']] == value['sha256'],
                               'tool changed during version query: ' + name)
            includes = {group: policy.include_arguments(group)[0] for group in policy.GROUPS}
            report['include_arguments'] = includes
            timeout = report['environment']['EC_TIMEOUT']
            policy.require(timeout == 60, 'reviewed prover timeout must remain 60 seconds')
            server = []
            if os.environ.get('WHY3_SERVER_SOCKET'):
                socket = Path(os.environ['WHY3_SERVER_SOCKET'])
                policy.require(socket.is_socket(), 'invalid Why3 server socket')
                server = ['-server', str(socket)]
            def command(path, group):
                return [easycrypt, 'compile', '-no-eco', '-pragmas', 'Proofs:check', '-p', 'Z3',
                        '-timeout', str(timeout), '-max-provers', '1', *server, *includes[group], path]
            def positive(index, name):
                path = BASE / name
                original = path.read_bytes()
                relative = str(path.relative_to(ROOT))
                policy.require(policy.sha(original) == pins[relative], 'proof changed before replay')
                sentinel = eof.SENTINELS[name]
                check_sentinel(name, sentinel, eof.SEMANTIC_TARGETS[name], eof.MODULE_BINDERS[name])
                directory = output / 'proof-inputs' / str(index)
                directory.mkdir(parents=True)
                copied = directory / path.name
                copied.write_text(completed_proof_text(original.decode('utf-8'), sentinel))
                checked_hash = digest(copied)
                log = run('proof-' + str(index).zfill(2) + '-' + path.stem, command(copied, Path(name).parts[0]), cwd=path.parent)
                policy.require(digest(copied) == checked_hash, 'checked copy changed')
                return {'source': relative, 'source_sha256': policy.sha(original),
                                             'checked_copy': str(copied), 'checked_copy_sha256': checked_hash,
                                             'sentinel_sha256': policy.sha(sentinel.encode()),
                                             'sentinel_placement': 'after last original proof closer, before trailing declarations or theory end',
                                             'semantic_target': eof.SEMANTIC_TARGETS[name],
                                             'explicit_module_binders': list(eof.MODULE_BINDERS[name]),
                                             'log': str(log), 'result': 'PASS'}

            def negative_proof(index, name):
                path = BASE / name
                original = path.read_bytes().decode('utf-8')
                negative = output / 'open-proof' / str(index) / path.name
                negative.parent.mkdir(parents=True)
                negative.write_text(unfinished_proof_text(original, eof.SENTINELS[name]))
                checked_hash = digest(negative)
                policy.require(checked_hash == report['negative_preflight'][index]['prepared_sha256'],
                               'negative copy differs from preflight')
                log = run('eof-open-proof-' + path.stem, command(negative, Path(name).parts[0]), True, path.parent)
                diagnostic = log.read_text(errors='replace')
                critical = check_negative_diagnostic(diagnostic, negative)
                policy.require(digest(negative) == checked_hash, 'negative copy changed')
                return {'source': str(path.relative_to(ROOT)), 'checked_copy': str(negative),
                                                  'source_sha256': policy.sha(original.encode()),
                                                  'sentinel_sha256': policy.sha(eof.SENTINELS[name].encode()),
                                                  'semantic_target': eof.SEMANTIC_TARGETS[name],
                                                  'explicit_module_binders': list(eof.MODULE_BINDERS[name]),
                                                  'checked_copy_sha256': checked_hash, 'log': str(log),
                                                  'critical_diagnostic': critical,
                                                  'rejection_scope': 'own isolated main, not an imported theory',
                                                  'result': 'EXPECTED_REJECTION'}

            report['proof_mains'] = run_phase(positive, policy.MAINS, jobs)
            save()
            # A failed positive phase raises before any negative is submitted.
            report['negative_proofs'] = run_phase(negative_proof, eof.NEGATIVE_PROOFS, jobs)
            save()
            policy.require(len(report['proof_mains']) == report['declared_proof_mains'], 'positive replay count')
            policy.require(len(report['negative_proofs']) == report['declared_negative_proofs'], 'negative replay count')
            report.update(status='PASS', new_authored_mains=len(policy.MAINS),
                          new_lemmas=sum(len(re.findall(r'(?m)^lemma\s+', (BASE / n).read_text())) for n in policy.MAINS))
    except Exception as error:
        report.update(status='FAIL', error_type=type(error).__name__, error=str(error))
    finally:
        try:
            if 'source_hashes_before' in report:
                report['source_hashes_after'] = policy.snapshot()
                report['inputs_unchanged'] = report['source_hashes_before'] == report['source_hashes_after']
                if not report['inputs_unchanged']:
                    report.update(status='FAIL', error='source inputs changed during replay')
            if 'external_hashes_before' in report:
                report['external_hashes_after'] = {str(p): digest(p) for p in sorted(external)}
                report['external_inputs_unchanged'] = report['external_hashes_before'] == report['external_hashes_after']
                if not report['external_inputs_unchanged']:
                    report.update(status='FAIL', error='tool/config/theory inputs changed during replay')
        except (OSError, ValueError) as error:
            report.update(status='FAIL', inputs_unchanged=False, error='final hash audit failed: ' + str(error))
        report['completed_at'] = timestamp()
        save()
    print(report['status'], summary)
    return 0 if report['status'] in ('PASS', 'SOURCE_CHECK_ONLY') else 1


if __name__ == '__main__':
    sys.exit(main())
