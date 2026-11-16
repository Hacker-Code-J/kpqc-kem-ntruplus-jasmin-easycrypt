#!/usr/bin/env python3
"""Check recorded evidence integrity and its binding to current proof sources.

This does not execute EasyCrypt or re-prove imported theorems.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

INDEX_SHA256 = "f168450b3134ad32e773f5d2fd79a26bb73ef178a03ed82b00b62fc54af5669a"
EXPECTED_PROJECT = "ntruplus"
EXPECTED_COUNTS = {'primary': 31, 'negative': 31, 'gate_runs': 0, 'gate_tests': 0}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def contained(root, relative):
    path = Path(relative)
    if path.is_absolute() or '..' in path.parts:
        raise ValueError('non-relative path: ' + relative)
    result = root / path
    if not result.resolve().is_relative_to(root.resolve()) or not result.is_file():
        raise ValueError('missing or escaping file: ' + relative)
    return result

def uncomment(text):
    depth, out = 0, []
    for token in re.split(r'(\(\*|\*\))', text):
        if token == '(*':
            depth += 1
            out.append(' ')
        elif token == '*)':
            if not depth:
                raise ValueError('unbalanced comment')
            depth -= 1
        elif not depth:
            out.append(token)
    if depth:
        raise ValueError('unclosed comment')
    return ''.join(out)

def declarations(text):
    return re.sub(r'\bproof\..*?\bqed\.', 'proof. qed.', uncomment(text), flags=re.S)

def unfinished(text, sentinel, tail_policy):
    depth, offset, closers = 0, 0, []
    for token in re.split(r'(\(\*|\*\))', text):
        if token == '(*':
            depth += 1
        elif token == '*)':
            depth -= 1
        elif depth == 0:
            closers.extend(offset + m.start() for m in re.finditer(r'\bqed\.', token))
        offset += len(token)
    if depth or not closers:
        raise ValueError('cannot locate final proof closer')
    cut = closers[-1]
    tail = text[cut + 4:]
    if tail_policy == 'drop-comment-whitespace-tail':
        if uncomment(tail).strip():
            raise ValueError('negative constructor would drop declarations')
        tail = ''
    elif tail_policy != 'preserve-tail':
        raise ValueError('unknown negative constructor')
    return text[:cut] + sentinel + tail

def check(repo, evidence):
    raw = contained(evidence, 'index.json').read_bytes()
    if digest(raw) != INDEX_SHA256:
        raise ValueError('index digest mismatch')
    index = json.loads(raw)
    if index['project'] != EXPECTED_PROJECT or index['counts'] != EXPECTED_COUNTS:
        raise ValueError('unexpected project/counts')
    for relative, expected in index['payloads'].items():
        if digest(contained(evidence, relative).read_bytes()) != expected:
            raise ValueError('payload digest mismatch: ' + relative)
    for relative, expected in index['source_bindings'].items():
        if digest(contained(repo, relative).read_bytes()) != expected:
            raise ValueError('current source digest mismatch: ' + relative)
    for change in index['proof_ports'] + index['import_variants']:
        original = contained(evidence, change['before_copy']).read_text()
        current = contained(repo, change['source']).read_text()
        if declarations(original) != declarations(current):
            raise ValueError('non-proof text changed: ' + change['source'])
    records = index['records']
    for kind, expected in EXPECTED_COUNTS.items():
        if kind == 'gate_tests':
            continue
        selected = [x for x in records if x['kind'] == kind]
        if len(selected) != expected or len({x['id'] for x in selected}) != expected:
            raise ValueError('record inventory mismatch: ' + kind)
    for record in records:
        log = contained(evidence, record['log']).read_text(errors='replace')
        if record['kind'] in ['primary', 'gate_runs']:
            if record['exit_code'] != 0 or '[critical]' in log:
                raise ValueError('non-successful primary/gate: ' + record['id'])
        else:
            if record['exit_code'] == 0 or record['critical_diagnostic'] not in log:
                raise ValueError('incorrect negative result: ' + record['id'])
        if record.get('checked_input') and record.get('source'):
            source = contained(repo, record['source']).read_text()
            sentinel = contained(evidence, record['sentinel']).read_text()
            expected = source + sentinel if record['kind'] == 'primary' else unfinished(source, sentinel, record['negative_tail_policy'])
            if contained(evidence, record['checked_input']).read_bytes() != expected.encode():
                raise ValueError('checked input does not match final source: ' + record['id'])
    return index

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--evidence-root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        index = check(args.repo_root.resolve(), args.evidence_root.resolve())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        return 1
    print('PASS: ' + index['project'] + ' recorded evidence and current proof-source integrity; '
          + str(index['counts']['primary']) + ' primary, '
          + str(index['counts']['negative']) + ' negative records. No prover execution.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
